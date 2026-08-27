#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>

template <int N>
struct Audit {
  static constexpr int P = 5;
  static constexpr int M = 2 * N;
  using Vec = std::array<std::uint8_t, N>;
  using Row = std::array<std::uint8_t, M>;
  using Pairing = std::array<std::array<std::uint8_t, 2>, N>;

  std::vector<Vec> norm_minus_one;
  std::vector<std::vector<std::uint64_t>> orthogonal;
  std::vector<Pairing> pairings;
  std::array<Vec, N> right{};
  std::uint64_t matrices = 0;
  std::uint64_t no_rank_one = 0;

  static int dot(const Vec &a, const Vec &b) {
    int result = 0;
    for (int i = 0; i < N; ++i) result += a[i] * b[i];
    return result % P;
  }

  static int inverse(int x) {
    static constexpr int inv[P] = {0, 1, 3, 2, 4};
    return inv[x];
  }

  static int rank(std::array<Vec, N> matrix) {
    int r = 0;
    for (int column = 0; column < N; ++column) {
      int pivot = r;
      while (pivot < N && matrix[pivot][column] == 0) ++pivot;
      if (pivot == N) continue;
      std::swap(matrix[r], matrix[pivot]);
      const int scale = inverse(matrix[r][column]);
      for (int j = column; j < N; ++j) matrix[r][j] =
          (matrix[r][j] * scale) % P;
      for (int i = r + 1; i < N; ++i) {
        const int multiple = matrix[i][column];
        if (!multiple) continue;
        for (int j = column; j < N; ++j) {
          matrix[i][j] =
              (matrix[i][j] + P - multiple * matrix[r][j] % P) % P;
        }
      }
      ++r;
    }
    return r;
  }

  void generate_vectors(int coordinate, Vec &vector) {
    if (coordinate == N) {
      if (dot(vector, vector) == P - 1) norm_minus_one.push_back(vector);
      return;
    }
    for (int value = 0; value < P; ++value) {
      vector[coordinate] = value;
      generate_vectors(coordinate + 1, vector);
    }
  }

  void generate_pairings(std::vector<int> remaining, Pairing &pairing,
                         int block) {
    if (remaining.empty()) {
      for (int orientation = 0; orientation < (1 << N); ++orientation) {
        Pairing oriented = pairing;
        for (int i = 0; i < N; ++i)
          if ((orientation >> i) & 1)
            std::swap(oriented[i][0], oriented[i][1]);
        pairings.push_back(oriented);
      }
      return;
    }
    const int first = remaining.front();
    for (int j = 1; j < static_cast<int>(remaining.size()); ++j) {
      const int second = remaining[j];
      std::vector<int> tail;
      for (int k = 1; k < static_cast<int>(remaining.size()); ++k)
        if (k != j) tail.push_back(remaining[k]);
      pairing[block] = {static_cast<std::uint8_t>(first),
                        static_cast<std::uint8_t>(second)};
      generate_pairings(tail, pairing, block + 1);
    }
  }

  bool has_rank_one(const Pairing &pairing) const {
    std::array<Row, N> generator{};
    for (int i = 0; i < N; ++i) {
      generator[i][i] = 1;
      for (int j = 0; j < N; ++j) generator[i][N + j] = right[i][j];
    }
    std::array<Vec, N> defect{};
    for (int i = 0; i < N; ++i)
      for (int block = 0; block < N; ++block) {
        const int first = pairing[block][0];
        const int second = pairing[block][1];
        defect[i][block] =
            (generator[i][second] + P - 2 * generator[i][first] % P) % P;
      }
    return N - rank(defect) == 1;
  }

  void inspect_matrix() {
    ++matrices;
    for (const Pairing &pairing : pairings)
      if (has_rank_one(pairing)) return;
    ++no_rank_one;
    std::cout << "candidate without rank-one pairing\n";
    for (const Vec &row : right) {
      for (int value : row) std::cout << value << ' ';
      std::cout << '\n';
    }
  }

  void generate_matrices(int depth, std::vector<std::uint64_t> available) {
    if (depth == N) {
      inspect_matrix();
      return;
    }
    for (std::size_t word = 0; word < available.size(); ++word) {
      std::uint64_t bits = available[word];
      while (bits) {
        const int offset = __builtin_ctzll(bits);
        const int index = static_cast<int>(64 * word + offset);
        bits &= bits - 1;
        if (index >= static_cast<int>(norm_minus_one.size())) continue;
        right[depth] = norm_minus_one[index];
        std::vector<std::uint64_t> next(available.size());
        for (std::size_t k = 0; k < available.size(); ++k)
          next[k] = available[k] & orthogonal[index][k];
        generate_matrices(depth + 1, std::move(next));
      }
    }
  }

  int run() {
    Vec vector{};
    generate_vectors(0, vector);
    const int words = (norm_minus_one.size() + 63) / 64;
    orthogonal.assign(norm_minus_one.size(),
                      std::vector<std::uint64_t>(words));
    for (int i = 0; i < static_cast<int>(norm_minus_one.size()); ++i)
      for (int j = 0; j < static_cast<int>(norm_minus_one.size()); ++j)
        if (dot(norm_minus_one[i], norm_minus_one[j]) == 0)
          orthogonal[i][j / 64] |= std::uint64_t{1} << (j % 64);

    Pairing pairing{};
    std::vector<int> coordinates(M);
    std::iota(coordinates.begin(), coordinates.end(), 0);
    generate_pairings(coordinates, pairing, 0);
    std::mt19937 generator(20260827);
    std::shuffle(pairings.begin(), pairings.end(), generator);

    std::vector<std::uint64_t> available(words, ~std::uint64_t{0});
    if (norm_minus_one.size() % 64)
      available.back() =
          (std::uint64_t{1} << (norm_minus_one.size() % 64)) - 1;
    generate_matrices(0, std::move(available));
    std::cout << "N=" << N << " norm_vectors=" << norm_minus_one.size()
              << " oriented_pairings=" << pairings.size()
              << " orthogonal_matrices=" << matrices
              << " without_rank_one=" << no_rank_one << '\n';
    return no_rank_one == 0 ? 0 : 1;
  }
};

int main(int argc, char **argv) {
  if (argc != 2) {
    std::cerr << "usage: rank_one_obstruction_audit 4|5\n";
    return 2;
  }
  const int n = std::stoi(argv[1]);
  if (n == 4) return Audit<4>().run();
  if (n == 5) return Audit<5>().run();
  std::cerr << "only N=4 and N=5 are certified\n";
  return 2;
}

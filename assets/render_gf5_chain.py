#!/usr/bin/env python3
"""Render the GF(5) chain in Propositions 4.1–4.2 from checked result data.

Requires Pillow. Run from any directory with ``python3 assets/render_gf5_chain.py``.
"""

import json
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "Formalization/Verification/Examples/applications_results.json"
OUTPUT = ROOT / "assets/gf5-building-up.gif"

W, H = 1080, 600
INK = "#1d2940"
MUTED = "#65738a"
BLUE = "#3159d9"
TEAL = "#087e78"
PURPLE = "#7b55a7"
GRID = "#dce3ed"


def font(kind, size):
    candidates = {
        "serif": ("/System/Library/Fonts/Supplemental/Georgia Bold.ttf",
                  "/usr/share/fonts/truetype/dejavu/DejaVuSerif-Bold.ttf"),
        "sans": ("/System/Library/Fonts/Supplemental/Arial.ttf",
                 "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"),
        "bold": ("/System/Library/Fonts/Supplemental/Arial Bold.ttf",
                 "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"),
        "mono": ("/System/Library/Fonts/Menlo.ttc",
                 "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf"),
    }
    return ImageFont.truetype(next(path for path in candidates[kind]
                                   if Path(path).exists()), size)


TITLE = font("serif", 37)
BODY = font("sans", 20)
BOLD = font("bold", 20)
SMALL = font("sans", 16)
SMALL_BOLD = font("bold", 16)
ARROW = font("bold", 27)
MATRIX = font("mono", 25)


def pair_blocks(matrix):
    return [[f"{row[2*j]}{row[2*j+1]}" for j in range(len(row) // 2)]
            for row in matrix]


def load_chain():
    examples = json.loads(RESULTS.read_text())["examples"]
    by_id = {item["id"]: item for item in examples}
    g6 = by_id["gf5_6"]["matrix"]
    g8 = by_id["gf5_8"]["matrix"]
    g4 = [row[2:] for row in g6[1:]]
    assert [row[2:] for row in g8[1:]] == g6
    assert [len(g4), len(g6), len(g8)] == [2, 3, 4]
    assert [len(g4[0]), len(g6[0]), len(g8[0])] == [4, 6, 8]
    assert [by_id["gf5_6"]["distance"], by_id["gf5_8"]["distance"]] == [4, 4]
    blocks = [pair_blocks(g4), pair_blocks(g6), pair_blocks(g8)]
    assert [row[1:] for row in blocks[2][1:]] == blocks[1]
    assert [row[1:] for row in blocks[1][1:]] == blocks[0]
    return blocks


def centered(draw, xy, text, face, fill):
    x, y = xy
    box = draw.textbbox((0, 0), text, font=face)
    draw.text((x - (box[2] - box[0]) / 2, y - (box[3] - box[1]) / 2 - box[1]),
              text, font=face, fill=fill)


def draw_frame(blocks, stage):
    image = Image.new("RGB", (W, H), "#f3f6fb")
    d = ImageDraw.Draw(image)
    d.rounded_rectangle((20, 18, W - 20, H - 18), radius=24,
                        fill="#ffffff", outline="#e8edf4", width=2)

    d.text((57, 49), "One code inside the next", font=TITLE, fill=INK)
    d.text((59, 105), "The exact GF(5) examples from Propositions 4.1–4.2",
           font=BODY, fill=MUTED)
    d.rounded_rectangle((851, 53, 1018, 96), radius=21,
                        fill="#e9f6f3", outline="#abd8d0", width=1)
    centered(d, (934, 74), "GF(5)  ·  2² = −1", BOLD, TEAL)
    d.line((58, 150, 1022, 150), fill="#e9edf4", width=2)

    d.text((76, 176), f"BLOCK MATRIX M{stage + 2}  ·  TWO COORDINATES PER CELL",
           font=SMALL_BOLD, fill=MUTED)

    # The 4×4 block matrix contains the 3×3 and 2×2 parents in its lower right.
    x0, y0, cw, ch = 79, 217, 99, 67
    start = 2 - stage
    full = blocks[2]
    for row in range(4):
        for col in range(4):
            left, top = x0 + col * cw, y0 + row * ch
            active = row >= start and col >= start
            if not active:
                fill, outline, value = "#fafbfd", "#e8ecf2", ""
            elif row >= 2 and col >= 2:
                fill, outline, value = "#f3eafb", "#d8c5e9", full[row][col]
            elif row == start or col == start:
                fill, outline, value = "#eaf0ff", "#adc1f5", full[row][col]
            else:
                fill, outline, value = "#e7f5f2", "#a7d8d0", full[row][col]
            d.rounded_rectangle((left, top, left + cw - 5, top + ch - 5),
                                radius=9, fill=fill, outline=outline, width=2)
            if value:
                centered(d, (left + (cw - 5) / 2, top + (ch - 5) / 2),
                         value, MATRIX, INK)
    d.line((x0 + start * cw - 8, y0 - 7,
            x0 + start * cw - 8, y0 + 4 * ch - 6), fill=BLUE, width=4)
    d.line((x0 - 8, y0 + start * ch - 8,
            x0 + 4 * cw - 6, y0 + start * ch - 8), fill=BLUE, width=4)

    # A compact reading guide stays visible throughout the animation.
    legend_y = 510
    for x, color, label in [(80, PURPLE, "seed"), (186, TEAL, "retained parent"),
                            (382, BLUE, "new row + pair")]:
        d.ellipse((x, legend_y + 4, x + 13, legend_y + 17), fill=color)
        d.text((x + 21, legend_y), label, font=SMALL, fill=MUTED)

    d.text((552, 178), "A two-coordinate building-up chain", font=BOLD, fill=INK)
    labels = [("C4", "[4, 2, 2]"), ("C6", "[6, 3, 4]"), ("C8", "[8, 4, 4]")]
    for index, (name, parameters) in enumerate(labels):
        x = 553 + index * 157
        current = index == stage
        completed = index < stage
        fill = "#eaf0ff" if current else ("#e7f5f2" if completed else "#f8fafc")
        outline = BLUE if current else ("#a7d8d0" if completed else GRID)
        d.rounded_rectangle((x, 220, x + 140, 286), radius=12,
                            fill=fill, outline=outline, width=2)
        centered(d, (x + 70, 240), name, SMALL_BOLD, BLUE if current else INK)
        centered(d, (x + 70, 266), parameters, SMALL, INK)
        if index < 2:
            d.text((x + 143, 239), "›", font=ARROW, fill="#a9b5c4")

    d.rounded_rectangle((551, 315, 1007, 461), radius=18,
                        fill="#f7f9fc", outline="#e4eaf2", width=2)
    headings = ["Start with the parent", "First building-up step",
                "Repeat the same step"]
    lines = [
        ("The 2×2 block matrix gives a", "self-dual [4, 2, 2] code."),
        ("One new row and coordinate pair", "give the optimal [6, 3, 4] code."),
        ("The [8, 4, 4] child contains the", "entire [6, 3, 4] parent matrix."),
    ]
    d.text((575, 338), headings[stage], font=BOLD, fill=BLUE)
    d.text((575, 382), lines[stage][0], font=BODY, fill=INK)
    d.text((575, 413), lines[stage][1], font=BODY, fill=INK)

    d.text((554, 486), "M4[1:, 1:] = M3    ·    M3[1:, 1:] = M2", font=SMALL_BOLD,
           fill=TEAL)
    d.line((58, 547, 1022, 547), fill="#e9edf4", width=2)
    d.text((60, 557), "Delete the newest block row and coordinate pair to recover the parent.",
           font=SMALL, fill=MUTED)
    return image


def main():
    blocks = load_chain()
    stills = [draw_frame(blocks, stage) for stage in range(3)]
    frames, durations = [], []
    sequence = [0, 1, 2, 1, 0]
    holds = [1300, 1400, 2100, 650, 900]
    for position, stage in enumerate(sequence):
        frames.append(stills[stage])
        durations.append(holds[position])
        if position + 1 < len(sequence):
            target = stills[sequence[position + 1]]
            for blend in (0.33, 0.67):
                frames.append(Image.blend(stills[stage], target, blend))
                durations.append(140)
    frames[0].save(OUTPUT, save_all=True, append_images=frames[1:],
                   duration=durations, loop=0, optimize=True, disposal=2)
    print(f"Wrote {OUTPUT} ({len(frames)} frames)")


if __name__ == "__main__":
    main()

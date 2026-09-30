/-
# Coordinates on the closed cells of `Q̄`

The face lattice of `Q̄` has `865` cells, indexed by `QbarCell = Fin 865`.  For a cell `e` and a
degree `k` this file fixes the *computable* enumeration

* `dimList k` — the indices of the `k`-cells of `Q̄`, in increasing order (as literal data),
* `dimListLe e k` — the indices of the `k`-cells below `e`, in increasing order,

and the induced bijection `cellOf e k : Fin (dimListLe e k).length → {f // f ≤ e ∧ dim f = k}`.

The `k`-cells below `e` are those members of the literal list `dimList k` satisfying the *cheap*
face relation `qLeC e` of `QbarTightCheap.lean`: the kernel can therefore evaluate
`dimListLe e k` quickly, which is what the per-cell certificates of `CxData/` compare their
literal enumerations against.

It also provides the *abstract boundary matrix* `bdData e k` of the closed cell of `e`, computed
from the incidence data `qFacet`/`qInc` of `Data/QbarFacet.lean`, and the lemma `bdData_toMatrix`
identifying it with the coordinates of the geometric differential `QbarCW.cellD`.

Everything here is at the level of the literal data on `Fin 865`, so that the kernel can evaluate
it: the geometric differential itself cannot be evaluated, because `Finsupp.single` is defined
through `Classical.decEq`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.CW
import Submission.Work.MbarHomology.Qbar.QbarTightCheap
import Submission.Work.MbarHomology.Qbar.CellDApply
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.MbarHomology

open Work.Subdivision

/-- The indices of the faces of `Q̄` of dimension `k`, in increasing order. -/
def dimList : ℕ → List (Fin 865)
  | 0 => [578, 579, 581, 582, 584, 585, 587, 588, 590, 591, 593, 594, 596, 597, 599, 600, 602, 603, 605, 606, 608, 609, 611, 612, 614, 615, 617, 618, 620, 621, 623, 624, 626, 627, 629, 630, 632, 633, 635, 636, 638, 639, 641, 642, 644, 645, 647, 648, 650, 651, 653, 654, 656, 657, 659, 660, 662, 663, 665, 666, 668, 669, 671, 672, 674, 675, 677, 678, 680, 681, 683, 684, 686, 687, 689, 690, 692, 693, 695, 696, 698, 699, 701, 702, 704, 705, 707, 708, 710, 711, 713, 714, 716, 717, 719, 720, 722, 723, 725, 726, 728, 729, 731, 732, 734, 735, 737, 738, 740, 741, 743, 744, 746, 747, 749, 750, 752, 753, 755, 756, 758, 759, 761, 762, 764, 765, 767, 768, 770, 771, 773, 774, 776, 777, 779, 780, 782, 783, 785, 786, 788, 789, 791, 792, 794, 795, 797, 798, 800, 801, 803, 804, 806, 807, 809, 810, 812, 813, 815, 816, 818, 819, 821, 822, 824, 825, 827, 828, 830, 831, 833, 834, 836, 837, 839, 840, 842, 843, 845, 846, 848, 849, 851, 852, 854, 855, 857, 858, 860, 861, 863, 864]
  | 1 => [194, 195, 196, 198, 199, 200, 202, 203, 204, 206, 207, 208, 210, 211, 212, 214, 215, 216, 218, 219, 220, 222, 223, 224, 226, 227, 228, 230, 231, 232, 234, 235, 236, 238, 239, 240, 242, 243, 244, 246, 247, 248, 250, 251, 252, 254, 255, 256, 258, 259, 260, 262, 263, 264, 266, 267, 268, 270, 271, 272, 274, 275, 276, 278, 279, 280, 282, 283, 284, 286, 287, 288, 290, 291, 292, 294, 295, 296, 298, 299, 300, 302, 303, 304, 306, 307, 308, 310, 311, 312, 314, 315, 316, 318, 319, 320, 322, 323, 324, 326, 327, 328, 330, 331, 332, 334, 335, 336, 338, 339, 340, 342, 343, 344, 346, 347, 348, 350, 351, 352, 354, 355, 356, 358, 359, 360, 362, 363, 364, 366, 367, 368, 370, 371, 372, 374, 375, 376, 378, 379, 380, 382, 383, 384, 386, 387, 388, 390, 391, 392, 394, 395, 396, 398, 399, 400, 402, 403, 404, 406, 407, 408, 410, 411, 412, 414, 415, 416, 418, 419, 420, 422, 423, 424, 426, 427, 428, 430, 431, 432, 434, 435, 436, 438, 439, 440, 442, 443, 444, 446, 447, 448, 450, 451, 452, 454, 455, 456, 458, 459, 460, 462, 463, 464, 466, 467, 468, 470, 471, 472, 474, 475, 476, 478, 479, 480, 482, 483, 484, 486, 487, 488, 490, 491, 492, 494, 495, 496, 498, 499, 500, 502, 503, 504, 506, 507, 508, 510, 511, 512, 514, 515, 516, 518, 519, 520, 522, 523, 524, 526, 527, 528, 530, 531, 532, 534, 535, 536, 538, 539, 540, 542, 543, 544, 546, 547, 548, 550, 551, 552, 554, 555, 556, 558, 559, 560, 562, 563, 564, 566, 567, 568, 570, 571, 572, 574, 575, 576, 577, 580, 583, 586, 589, 592, 595, 598, 601, 604, 607, 610, 613, 616, 619, 622, 625, 628, 631, 634, 637, 640, 643, 646, 649, 652, 655, 658, 661, 664, 667, 670, 673, 676, 679, 682, 685, 688, 691, 694, 697, 700, 703, 706, 709, 712, 715, 718, 721, 724, 727, 730, 733, 736, 739, 742, 745, 748, 751, 754, 757, 760, 763, 766, 769, 772, 775, 778, 781, 784, 787, 790, 793, 796, 799, 802, 805, 808, 811, 814, 817, 820, 823, 826, 829, 832, 835, 838, 841, 844, 847, 850, 853, 856, 859, 862]
  | 2 => [26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 73, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 89, 90, 91, 92, 93, 94, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 108, 110, 111, 112, 113, 114, 115, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 138, 139, 140, 141, 142, 143, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 197, 201, 205, 209, 213, 217, 221, 225, 229, 233, 237, 241, 245, 249, 253, 257, 261, 265, 269, 273, 277, 281, 285, 289, 293, 297, 301, 305, 309, 313, 317, 321, 325, 329, 333, 337, 341, 345, 349, 353, 357, 361, 365, 369, 373, 377, 381, 385, 389, 393, 397, 401, 405, 409, 413, 417, 421, 425, 429, 433, 437, 441, 445, 449, 453, 457, 461, 465, 469, 473, 477, 481, 485, 489, 493, 497, 501, 505, 509, 513, 517, 521, 525, 529, 533, 537, 541, 545, 549, 553, 557, 561, 565, 569, 573]
  | 3 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 32, 39, 46, 53, 60, 67, 74, 81, 88, 95, 102, 109, 116, 123, 130, 137, 144, 151, 158, 165, 172, 179, 186]
  | 4 => [0]
  | _ => []

theorem dimList_nil5 (k : ℕ) : dimList (k+5) = [] := rfl

theorem mem_dimList0 : ∀ i : Fin 865, i ∈ dimList 0 ↔ QbarCW.dim (⟨i⟩ : QbarCell) = 0 := by
  decide

theorem mem_dimList1 : ∀ i : Fin 865, i ∈ dimList 1 ↔ QbarCW.dim (⟨i⟩ : QbarCell) = 1 := by
  decide

theorem mem_dimList2 : ∀ i : Fin 865, i ∈ dimList 2 ↔ QbarCW.dim (⟨i⟩ : QbarCell) = 2 := by
  decide

theorem mem_dimList3 : ∀ i : Fin 865, i ∈ dimList 3 ↔ QbarCW.dim (⟨i⟩ : QbarCell) = 3 := by
  decide

theorem mem_dimList4 : ∀ i : Fin 865, i ∈ dimList 4 ↔ QbarCW.dim (⟨i⟩ : QbarCell) = 4 := by
  decide

theorem mem_dimList {k : ℕ} {i : Fin 865} :
    i ∈ dimList k ↔ QbarCW.dim (⟨i⟩ : QbarCell) = k := by
  match k with
  | 0 => exact mem_dimList0 i
  | 1 => exact mem_dimList1 i
  | 2 => exact mem_dimList2 i
  | 3 => exact mem_dimList3 i
  | 4 => exact mem_dimList4 i
  | k+5 =>
      rw [dimList_nil5]
      constructor
      · intro h; exact absurd h (List.not_mem_nil)
      · intro h
        have h4 : QbarCW.dim (⟨i⟩ : QbarCell) ≤ 4 := by rw [QbarCW_dim]; omega
        omega

theorem dimList_nodup (k : ℕ) : (dimList k).Nodup := by
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | k+5 => rw [dimList_nil5]; exact List.nodup_nil

/-- There are no faces of `Q̄` above dimension four. -/
theorem dimList_eq_nil {k : ℕ} (hk : 4 < k) : dimList k = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro i hi
  have h := mem_dimList.1 hi
  have h4 : QbarCW.dim (⟨i⟩ : QbarCell) ≤ 4 := by rw [QbarCW_dim]; omega
  omega

/-- The indices of the faces of `Q̄` of dimension `k` that lie below `e`, in increasing order. -/
def dimListLe (e : Fin 865) (k : ℕ) : List (Fin 865) :=
  (dimList k).filter (fun i => decide (qLeC e i))

theorem mem_dimListLe {e : Fin 865} {k : ℕ} {i : Fin 865} :
    i ∈ dimListLe e k ↔
      (QbarCW.dim (⟨i⟩ : QbarCell) = k ∧ (⟨i⟩ : QbarCell) ≤ (⟨e⟩ : QbarCell)) := by
  rw [dimListLe, List.mem_filter, mem_dimList, decide_eq_true_iff, qLeC_iff]

theorem dimListLe_nodup (e : Fin 865) (k : ℕ) : (dimListLe e k).Nodup :=
  (dimList_nodup k).filter _

/-- **The coordinates of the `k`-cells of the closed cell of `e`.** -/
def cellOf (e : Fin 865) (k : ℕ) :
    Fin (dimListLe e k).length → {f : QbarCell // f ≤ (⟨e⟩ : QbarCell) ∧ QbarCW.dim f = k} :=
  fun i => ⟨⟨(dimListLe e k).get i⟩, by
    rcases (mem_dimListLe.1 (List.get_mem _ i)) with ⟨h1, h2⟩
    exact ⟨h2, h1⟩⟩

/-- The `i`-th `k`-cell below `e`, as a cell of dimension exactly `k`. -/
def cellTop (e : Fin 865) (k : ℕ) (i : Fin (dimListLe e k).length) :
    {f : QbarCell // QbarCW.dim f = k} :=
  ⟨(cellOf e k i).1, (cellOf e k i).2.2⟩

@[simp] theorem cellTop_val (e : Fin 865) (k : ℕ) (i : Fin (dimListLe e k).length) :
    (cellTop e k i).1 = ⟨(dimListLe e k).get i⟩ := rfl

theorem cellOf_le (e : Fin 865) (k : ℕ) (i : Fin (dimListLe e k).length) :
    (cellOf e k i).1 ≤ (⟨e⟩ : QbarCell) := (cellOf e k i).2.1

theorem cellTop_dim (e : Fin 865) (k : ℕ) (i : Fin (dimListLe e k).length) :
    QbarCW.dim (cellTop e k i).1 = k := (cellTop e k i).2

/-- The homology ranks of the closed cell of a face of `Q̄`: a disk has `ℤ` in degree `0` and
nothing above. -/
def bModel (k : ℕ) : ℕ := if k = 0 then 1 else 0

@[simp] theorem bModel_zero : bModel 0 = 1 := rfl

theorem bModel_eq_zero {k : ℕ} (hk : k ≠ 0) : bModel k = 0 := if_neg hk

/-- The closed cell of a face of dimension `< k` has no cells below it in degree `k`. -/
theorem dimListLe_eq_nil (e : Fin 865) (k : ℕ) (hk : 4 < k) : dimListLe e k = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro i hi
  have h := (mem_dimListLe.1 hi).1
  have h4 : QbarCW.dim (⟨i⟩ : QbarCell) ≤ 4 := by rw [QbarCW_dim]; omega
  omega

/-- Below the dimension of `e` there are no cells of dimension `k`. -/
theorem dimListLe_eq_nil_of_dim_lt {e : Fin 865} {k : ℕ}
    (hk : QbarCW.dim (⟨e⟩ : QbarCell) < k) : dimListLe e k = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro i hi
  obtain ⟨hd, hle⟩ := mem_dimListLe.1 hi
  have h1 : QbarCW.dim (⟨i⟩ : QbarCell) ≤ QbarCW.dim (⟨e⟩ : QbarCell) := QbarCW.dim_le hle
  omega

/-- The enumeration `cellOf e k` is injective. -/
theorem cellOf_injective (e : Fin 865) (k : ℕ) : Function.Injective (cellOf e k) := by
  intro i j hij
  have h1 : (dimListLe e k).get i = (dimListLe e k).get j := by
    simpa [cellOf] using congrArg (fun f => f.1.idx) hij
  exact (dimListLe_nodup e k).get_inj_iff.mp h1

/-- The enumeration `cellTop e k` of the `k`-cells below `e`, as cells of dimension `k`. -/
theorem cellTop_injective (e : Fin 865) (k : ℕ) : Function.Injective (cellTop e k) := by
  intro i j hij
  have h1 : (cellOf e k i).1 = (cellOf e k j).1 :=
    congrArg (fun x : {f : QbarCell // QbarCW.dim f = k} => x.1) hij
  exact cellOf_injective e k (Subtype.ext h1)

/-! ### The data-level description of the incidence relation -/

/-- The incidence numbers of `QbarCW` are the data-level incidence numbers `qInc`. -/
theorem inc_eq (f g : Fin 865) :
    QbarCW.inc (⟨f⟩ : QbarCell) (⟨g⟩ : QbarCell) = qInc f g := rfl

/-! ### The abstract boundary matrix of the closed cell of `e` -/

/-- The `(i,j)` entry of the boundary matrix of the closed cell of `e`: the incidence number of
the `i`-th `k`-cell below `e` in the boundary of the `j`-th `(k+1)`-cell below `e`. -/
def bdEntry (e : Fin 865) (k : ℕ) (i : Fin (dimListLe e k).length)
    (j : Fin (dimListLe e (k+1)).length) : ℤ :=
  if ((dimListLe e k).get i) ∈ qFacet ((dimListLe e (k+1)).get j) then
    qInc ((dimListLe e (k+1)).get j) ((dimListLe e k).get i) else 0

/-- **The abstract boundary matrix of the closed cell of `e`**, as sparse data: the `j`-th column
is the boundary of the `j`-th `(k+1)`-cell below `e`, written in the coordinates `cellOf e k`
(the non-zero entries only). -/
def bdData (e : Fin 865) (k : ℕ) :
    Work.Certificates.SOp (dimListLe e k).length (dimListLe e (k+1)).length :=
  ⟨fun j => ((List.finRange (dimListLe e k).length).filterMap fun i =>
      if bdEntry e k i j = 0 then none else some (i, bdEntry e k i j))⟩

end Work.MbarHomology

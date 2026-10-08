import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.mem_cmtK0_iff_exists
import Submission.Work.L2F.Props.conj_eq_inv_of_mem_cmtK0
import Submission.Work.L2F.Props.conj_T_cmtK1_mem
import Submission.Work.L2F.Props.cmtK1_mul_mem_cmtK0
import Submission.Work.L2F.Props.cmtK1_inv_mem

open scoped MatrixGroups
open scoped commutatorElement
open Matrix

namespace Work.L2F.Props

/-- In a group where `g` is an involution, `Subgroup.zpowers g` has exactly two elements `1` and
`g`: for `g ^ i` with `i` even this is `(g ^ 2) ^ (i / 2) = 1`, and with `i` odd it is
`(g ^ 2) ^ ((i - 1) / 2) * g = g`. -/
private lemma zpowers_sq_eq_one_of_sq_eq_one {G : Type*} [Group G] {g x : G} (hg : g ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  have hg' : g ^ (2 : ℤ) = 1 := by simpa using hg
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← hi]
  rcases Int.even_or_odd i with h | h
  · left
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp h
    rw [hk, _root_.zpow_mul, hg', _root_.one_zpow]
  · right
    have h1 : Even (i - 1) := h.sub_odd odd_one
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp h1
    have hi' : i = (i - 1) + 1 := by ring
    rw [hi', _root_.zpow_add, hk, _root_.zpow_mul, hg', _root_.one_zpow, one_mul, zpow_one]

/-- `[⟨t⟩, C_{L₂(F)}(s)]` is the "rotation subgroup" of the torus: the commutator of
`⟨toPGL T⟩` with the image of `cmtK F S` is the image of `cmtK0 F S`, the centralizer of `S`
in `SL(2,F)`.  Useful inputs already in the workspace (import as needed):
`Work.L2F.Props.mem_cmtK0_iff_exists` (writes elements of `cmtK0 F S` as `a • 1 + b • S`),
`Work.L2F.Props.cmtK0_mulEquiv_hypTorus` (cyclicity of `cmtK0 F S`).  Sketch: `⁅T,x⁆ = T x T⁻¹ x⁻¹`;
for `x ∈ cmtK0` one has `T x T⁻¹ = x⁻¹`, so `⁅T,x⁆ = x ^ (-2)`; for `x ∈ cmtK1` conjugation by `T`
stays in `cmtK1` and a product of two `cmtK1`-elements lies in `cmtK0`, so `⁅T,x⁆ ∈ cmtK0` again;
this gives `≤`.  For `≥`: the image of `cmtK0 F S` has odd order `m` (`hodd`), so `y ^ m = 1` and
`y = (y ^ ((m+1)/2)) ^ 2`; as `⁅toPGL T, toPGL x⁆ = toPGL (x ^ (-2))`, the whole image lies in the
commutator subgroup. -/
theorem commutator_zpowers_map_cmtK_eq (F : Type*) [Field F] [Fintype F]
    (S : Matrix.GeneralLinearGroup (Fin 2) F) (T : Matrix.SpecialLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hT2 : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1)
    (hST : Matrix.SpecialLinearGroup.toGL T * S = Work.L2F.Props.negGL F S *
      Matrix.SpecialLinearGroup.toGL T)
    (hodd : Odd (Nat.card ((Work.L2F.Props.cmtK0 F S).map
      Matrix.SpecialLinearGroup.toPGL))) :
    ⁅Subgroup.zpowers (Matrix.SpecialLinearGroup.toPGL T),
        (Work.L2F.Props.cmtK F S).map Matrix.SpecialLinearGroup.toPGL⁆ =
      (Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL := by
  -- `toPGL T` is an involution: `T ^ 2 = -1` is central in `SL(2,F)`, so lies in `ker toPGL`.
  have hA2 : (Matrix.SpecialLinearGroup.toPGL T) ^ 2 = 1 := by
    have hTT : T * T = Work.L2F.negOne F := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, hT2]
      rfl
    have hcenter : Work.L2F.negOne F ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      rw [show (Work.L2F.negOne F : Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]
    have hneg : Matrix.SpecialLinearGroup.toPGL (Work.L2F.negOne F) = 1 :=
      MonoidHom.mem_ker.mp (by rw [Matrix.SpecialLinearGroup.toPGL_ker]; exact hcenter)
    calc (Matrix.SpecialLinearGroup.toPGL T) ^ 2
        = Matrix.SpecialLinearGroup.toPGL T * Matrix.SpecialLinearGroup.toPGL T := pow_two _
      _ = Matrix.SpecialLinearGroup.toPGL (T * T) := (map_mul _ _ _).symm
      _ = Matrix.SpecialLinearGroup.toPGL (Work.L2F.negOne F) := by rw [hTT]
      _ = 1 := hneg
  apply le_antisymm
  · -- `⁅⟨toPGL T⟩, L⁆ ≤ RHS`: on generators, `⁅toPGL T, toPGL x⁆` is the image of
    -- `⁅T, x⁆`, which lies in `cmtK0 F S` for both `x ∈ cmtK0` and `x ∈ cmtK1`.
    rw [Subgroup.commutator_le]
    intro a ha l hl
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨x, hxK, rfl⟩ := Subgroup.mem_map.mp hl
    rw [← hi]
    have hmem : (Matrix.SpecialLinearGroup.toPGL T) ^ i ∈
        Subgroup.zpowers (Matrix.SpecialLinearGroup.toPGL T) :=
      Subgroup.zpow_mem (Subgroup.zpowers (Matrix.SpecialLinearGroup.toPGL T))
        (Subgroup.mem_zpowers (Matrix.SpecialLinearGroup.toPGL T)) i
    rcases zpowers_sq_eq_one_of_sq_eq_one (g := Matrix.SpecialLinearGroup.toPGL T)
      (x := (Matrix.SpecialLinearGroup.toPGL T) ^ i) hA2 hmem with h | h
    · -- `(toPGL T) ^ i = 1`: the commutator is trivial.
      rw [h]
      simp
    · -- `(toPGL T) ^ i = toPGL T`: reduce to `⁅T, x⁆ ∈ cmtK0 F S`.
      rw [h, ← map_commutatorElement]
      apply Subgroup.mem_map_of_mem
      rw [commutatorElement_def]
      rcases (Work.L2F.Props.mem_cmtK_iff F S x).mp hxK with hx0 | hx1
      · -- `x ∈ cmtK0`: `T` inverts `x`, so `⁅T,x⁆ = x ^ (-2)`.
        have hx0' : x ∈ Work.L2F.Props.cmtK0 F S :=
          (Work.L2F.Props.mem_cmtK0_iff F S x).mpr hx0
        rw [Work.L2F.Props.conj_eq_inv_of_mem_cmtK0 F S T lam hS hlam hns hT2 hST hx0']
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx0') (Subgroup.inv_mem _ hx0')
      · -- `x ∈ cmtK1`: `⁅T,x⁆ = (T x T⁻¹) * x⁻¹` is a product of two `cmtK1`-elements.
        have hx1' : x ∈ Work.L2F.Props.cmtK1 F S :=
          (Work.L2F.Props.mem_cmtK1_iff F S x).mpr hx1
        exact Work.L2F.Props.cmtK1_mul_mem_cmtK0 F S (T * x * T⁻¹) x⁻¹
          (Work.L2F.Props.conj_T_cmtK1_mem F S T hST x hx1')
          (Work.L2F.Props.cmtK1_inv_mem F S x hx1')
  · -- `RHS ≤ ⁅⟨toPGL T⟩, L⁆`: for `y ∈ cmtK0`, `z = toPGL y` satisfies `z ^ m = 1` with `m` odd,
    -- while `⁅toPGL T, toPGL y⁆ = toPGL (⁅T,y⁆) = z ^ (-2)` lies in the commutator, so
    -- `z = (z ^ 2) ^ ((m+1)/2)` also lies there.
    intro z hz
    obtain ⟨y, hyK0, hyz⟩ := Subgroup.mem_map.mp hz
    rw [← hyz]
    have hyK : y ∈ Work.L2F.Props.cmtK F S := Work.L2F.Props.cmtK0_le_cmtK F S hyK0
    have hTL : Matrix.SpecialLinearGroup.toPGL T ∈
        Subgroup.zpowers (Matrix.SpecialLinearGroup.toPGL T) := Subgroup.mem_zpowers _
    have hyL : Matrix.SpecialLinearGroup.toPGL y ∈
        (Work.L2F.Props.cmtK F S).map Matrix.SpecialLinearGroup.toPGL :=
      Subgroup.mem_map_of_mem _ hyK
    have hcomm : ⁅Matrix.SpecialLinearGroup.toPGL T, Matrix.SpecialLinearGroup.toPGL y⁆ ∈
        ⁅Subgroup.zpowers (Matrix.SpecialLinearGroup.toPGL T),
          (Work.L2F.Props.cmtK F S).map Matrix.SpecialLinearGroup.toPGL⁆ :=
      Subgroup.commutator_mem_commutator hTL hyL
    -- `⁅T, y⁆ = y ^ (-2)` because `T` inverts `cmtK0 F S`.
    have hb := Work.L2F.Props.conj_eq_inv_of_mem_cmtK0 F S T lam hS hlam hns hT2 hST hyK0
    have hkey : Matrix.SpecialLinearGroup.toPGL ⁅T, y⁆ =
        (Matrix.SpecialLinearGroup.toPGL y) ^ (-2 : ℤ) := by
      rw [commutatorElement_def, hb]
      simp only [_root_.map_mul, _root_.map_inv, _root_.zpow_neg, zpow_ofNat, pow_two,
        _root_.mul_inv_rev]
    have hkey2 : ⁅Matrix.SpecialLinearGroup.toPGL T, Matrix.SpecialLinearGroup.toPGL y⁆ =
        (Matrix.SpecialLinearGroup.toPGL y) ^ (-2 : ℤ) := by
      rw [← map_commutatorElement]
      exact hkey
    have hcomm2 : (Matrix.SpecialLinearGroup.toPGL y) ^ (-2 : ℤ) ∈
        ⁅Subgroup.zpowers (Matrix.SpecialLinearGroup.toPGL T),
          (Work.L2F.Props.cmtK F S).map Matrix.SpecialLinearGroup.toPGL⁆ := by
      rw [← hkey2]; exact hcomm
    have hz2 : (Matrix.SpecialLinearGroup.toPGL y) ^ 2 ∈
        ⁅Subgroup.zpowers (Matrix.SpecialLinearGroup.toPGL T),
          (Work.L2F.Props.cmtK F S).map Matrix.SpecialLinearGroup.toPGL⁆ := by
      have hinv := Subgroup.inv_mem _ hcomm2
      rwa [_root_.zpow_neg, zpow_ofNat, inv_inv] at hinv
    -- `z ^ m = 1` with `m = Nat.card ↥(cmtK0 F S).map toPGL`, by Lagrange on the image subgroup.
    have hzm : (Matrix.SpecialLinearGroup.toPGL y) ^
        (Nat.card ↥((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL)) = 1 := by
      have h := pow_card_eq_one'
        (x := (⟨Matrix.SpecialLinearGroup.toPGL y, Subgroup.mem_map_of_mem _ hyK0⟩ :
          ↥((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL)))
      simpa using congrArg Subtype.val h
    -- `m` is odd, so `2 * ((m + 1) / 2) = m + 1` and `z = (z ^ 2) ^ ((m + 1) / 2)`.
    have hm2 : 2 * ((Nat.card ↥((Work.L2F.Props.cmtK0 F S).map
        Matrix.SpecialLinearGroup.toPGL) + 1) / 2) =
        Nat.card ↥((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) + 1 := by
      obtain ⟨t, ht⟩ := hodd
      omega
    have hpow : ((Matrix.SpecialLinearGroup.toPGL y) ^ 2) ^
        ((Nat.card ↥((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) + 1) / 2) ∈
        ⁅Subgroup.zpowers (Matrix.SpecialLinearGroup.toPGL T),
          (Work.L2F.Props.cmtK F S).map Matrix.SpecialLinearGroup.toPGL⁆ :=
      Subgroup.pow_mem _ hz2 _
    have heq : ((Matrix.SpecialLinearGroup.toPGL y) ^ 2) ^
        ((Nat.card ↥((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) + 1) / 2) =
        Matrix.SpecialLinearGroup.toPGL y := by
      rw [← pow_mul, hm2, pow_succ, hzm, one_mul]
    rw [← heq]
    exact hpow

end Work.L2F.Props

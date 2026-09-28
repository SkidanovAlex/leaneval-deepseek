import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Q44Child.witness_class_count
import Submission.Work.HP.Q44Child.witness_outside
import Submission.Work.HP.Q44Child.latZero_bound
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDEstimates.WClassDefs
import Submission.Work.HP.MDEstimates.Q56.ratRepr
import Submission.Work.HP.MDEstimates.Q56.evalVerPolyQ

/-!
# The per-lattice count of `ℓ^{(56)}` (`Work.HP.MDEstimates.q44_perlat_56`)

For a rank-`3` sublattice `L ⊆ ℤ^5` with `λ₁(L) ≤ Z` and `λ₂(L) ≤ Z`, the number of
`ℤ`-linearly independent pairs of points of `L ∩ B(Z)` with `λ₅₆(Γ_{x,y}) ≤ J` is
`O(Z⁴ J¹⁵ λ₁¹⁸ λ₂¹⁸ λ₃²⁰)` (BLBS §3.4, the estimate `ℓ^{(56)}` of the quartic threefold
case).

Route: for each counted pair pick a witness form `a ∈ Γ_{x,y}`, `‖a‖ ≤ J`, `a ∉ W(L)`
(`Work.HP.Q44Child.witness_outside`); let `v = (v₁,v₂,v₃)` be three independent vectors of
`L` with `‖v_j‖ ≤ λ_j` (`Work.HP.FM.exists_indep_le_lam`).  The witness class `wClass v a`
determines the restriction of the form to `L` (`Per56.wclassDetermines`, from the rational
representation `Q56.ratRepr` and the evaluation identity `Q56.evalVerPolyQ`), and the number
of classes that occur is `≤ C J¹⁵ ∏_j ‖v_j‖²⁰ ≤ C J¹⁵ λ₁²⁰λ₂²⁰λ₃²⁰`
(`Work.HP.Q44Child.witness_class_count`).  For each class the points of `L ∩ B(Z)` on which
one (hence every) form of that class vanishes number at most
`C(1+Z/λ₁)(1+Z/λ₂) ≤ 4C Z²/(λ₁λ₂)` (`Work.HP.Q44Child.latZero_bound`), so each fibre of
pairs numbers at most the square of that.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.HP.MDEstimates

open MvPolynomial Finset

namespace Per56

/-- The pair set counted by the per-lattice estimate. -/
def pairSet (L : Submodule ℤ (Fin 5 → ℤ)) (Z J : ℝ) :
    Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | p.1 ∈ L ∧ p.2 ∈ L ∧ Work.HP.eNorm p.1 ≤ Z ∧ Work.HP.eNorm p.2 ≤ Z ∧
    LinearIndependent ℤ ![p.1, p.2] ∧ Work.HP.lam (Work.HP.Gam 4 4 p.1 p.2) 56 ≤ J}

/-- The points of `L` of norm at most `Z` at which the quartic form `a` vanishes. -/
def zeroSet (L : Submodule ℤ (Fin 5 → ℤ)) (a : Work.HP.Mon 4 4 → ℤ) (Z : ℝ) :
    Set (Fin 5 → ℤ) :=
  {x | x ∈ L ∧ Work.HP.eNorm x ≤ Z ∧ Work.HP.formEval 4 4 a x = 0}

/-- The evaluation of `formEval` at a rational point of the span of `v` is the witness-class
expansion. -/
lemma formEval_eq_wClass_sum (v : Fin 3 → (Fin 5 → ℤ)) (a : Work.HP.Mon 4 4 → ℤ)
    (s : Fin 3 → ℚ) :
    Work.HP.formEval 4 4 a (fun i => ∑ j : Fin 3, s j * (v j i : ℚ))
      = ∑ e : Work.HP.Tri4,
          ((Work.HP.wClass v a e : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
  have hinner : ∀ m : Work.HP.Mon 4 4,
      ∏ i : Fin 5, (∑ j : Fin 3, s j * (v j i : ℚ)) ^ (m.1 i : ℕ)
        = ∑ e : Work.HP.Tri4,
            ((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
    intro m
    rw [← eval_verPolyQ_lin v s m]
    exact Work.HP.MDEstimates.Q56.evalVerPolyQ v s m
  simp only [Work.HP.formEval, Work.HP.veronese]
  calc ∑ m : Work.HP.Mon 4 4,
        ((a m : ℤ) : ℚ) * ∏ i : Fin 5, (∑ j : Fin 3, s j * (v j i : ℚ)) ^ (m.1 i : ℕ)
      = ∑ m : Work.HP.Mon 4 4, ((a m : ℤ) : ℚ) *
          (∑ e : Work.HP.Tri4, ((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) *
            ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j)) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hinner m]
    _ = ∑ m : Work.HP.Mon 4 4, ∑ e : Work.HP.Tri4, ((a m : ℤ) : ℚ) *
          (((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j)) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ e : Work.HP.Tri4, ∑ m : Work.HP.Mon 4 4, ((a m : ℤ) : ℚ) *
          (((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j)) :=
        Finset.sum_comm
    _ = ∑ e : Work.HP.Tri4,
          (∑ m : Work.HP.Mon 4 4, ((a m : ℤ) : ℚ) * ((Work.HP.wCoeff v e.1 m : ℤ) : ℚ)) *
            ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun m _ => by ring)
    _ = ∑ e : Work.HP.Tri4,
          ((Work.HP.wClass v a e : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        congr 1
        rw [Work.HP.wClass]
        push_cast
        rfl

/-- Two quartic forms with the same witness class relative to an independent triple `v` that
spans `L` over `ℚ` agree at every point of `L`. -/
theorem wclassDetermines {L : Submodule ℤ (Fin 5 → ℤ)} (hL : Work.HP.rk L = 3)
    {v : Fin 3 → (Fin 5 → ℤ)} (hv : LinearIndependent ℤ v) (hvL : ∀ j, v j ∈ L)
    {a a' : Work.HP.Mon 4 4 → ℤ} (h : Work.HP.wClass v a = Work.HP.wClass v a') :
    ∀ u : Fin 5 → ℤ, u ∈ L → Work.HP.formEval 4 4 a u = Work.HP.formEval 4 4 a' u := by
  intro u hu
  obtain ⟨s, hs⟩ := Work.HP.MDEstimates.Q56.ratRepr hL hv hvL hu
  have key : ∀ b : Work.HP.Mon 4 4 → ℤ,
      ((Work.HP.formEval 4 4 b u : ℤ) : ℚ)
        = ∑ e : Work.HP.Tri4,
            ((Work.HP.wClass v b e : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
    intro b
    have h1 : ((Work.HP.formEval 4 4 b u : ℤ) : ℚ)
        = Work.HP.formEval 4 4 b (fun i => (u i : ℚ)) := by
      simp only [Work.HP.formEval, Work.HP.veronese]
      push_cast
      rfl
    have h2 : Work.HP.formEval 4 4 b (fun i => (u i : ℚ))
        = Work.HP.formEval 4 4 b (fun i => ∑ j : Fin 3, s j * (v j i : ℚ)) := by
      congr 1
      funext i
      exact hs i
    rw [h1, h2, formEval_eq_wClass_sum]
  have hcast : ((Work.HP.formEval 4 4 a u : ℤ) : ℚ)
      = ((Work.HP.formEval 4 4 a' u : ℤ) : ℚ) := by
    rw [key a, key a']
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [h]
  exact Int.cast_injective hcast

/-- The arithmetic core of the per-lattice estimate. -/
lemma perlatArith (Cw Cz Z J l1 l2 l3 P : ℝ) (hCw : 0 < Cw) (hCz : 0 < Cz) (hJ : 0 < J)
    (hZ : 0 < Z) (hl1 : 0 < l1) (hl2 : 0 < l2) (hl3 : 0 < l3) (h1Z : l1 ≤ Z) (h2Z : l2 ≤ Z)
    (hP : P ≤ l1 ^ 20 * l2 ^ 20 * l3 ^ 20) :
    Cw * J ^ 15 * P * (Cz * (1 + Z / l1) * (1 + Z / l2)) ^ 2 ≤
      Cw * Cz ^ 2 * 16 * Z ^ 4 * J ^ 15 * l1 ^ 18 * l2 ^ 18 * l3 ^ 20 := by
  have e1 : l1 * (1 + Z / l1) = l1 + Z := by field_simp
  have e2 : l2 * (1 + Z / l2) = l2 + Z := by field_simp
  have ha : (l1 * (1 + Z / l1)) ^ 2 ≤ 4 * Z ^ 2 := by
    have h : l1 * (1 + Z / l1) ≤ 2 * Z := by linarith
    nlinarith [sq_nonneg (l1 * (1 + Z / l1)), sq_nonneg (2 * Z)]
  have hb : (l2 * (1 + Z / l2)) ^ 2 ≤ 4 * Z ^ 2 := by
    have h : l2 * (1 + Z / l2) ≤ 2 * Z := by linarith
    nlinarith [sq_nonneg (l2 * (1 + Z / l2)), sq_nonneg (2 * Z)]
  have hmain : P * (l1 * (1 + Z / l1)) ^ 2 * (l2 * (1 + Z / l2)) ^ 2 ≤
      16 * Z ^ 4 * l1 ^ 20 * l2 ^ 20 * l3 ^ 20 := by
    have h1 : P * (l1 * (1 + Z / l1)) ^ 2 ≤ (l1 ^ 20 * l2 ^ 20 * l3 ^ 20) * (4 * Z ^ 2) :=
      mul_le_mul hP ha (by positivity) (by positivity)
    have h2 : P * (l1 * (1 + Z / l1)) ^ 2 * (l2 * (1 + Z / l2)) ^ 2 ≤
        ((l1 ^ 20 * l2 ^ 20 * l3 ^ 20) * (4 * Z ^ 2)) * (4 * Z ^ 2) :=
      mul_le_mul h1 hb (by positivity) (by positivity)
    calc P * (l1 * (1 + Z / l1)) ^ 2 * (l2 * (1 + Z / l2)) ^ 2 ≤
          ((l1 ^ 20 * l2 ^ 20 * l3 ^ 20) * (4 * Z ^ 2)) * (4 * Z ^ 2) := h2
      _ = 16 * Z ^ 4 * l1 ^ 20 * l2 ^ 20 * l3 ^ 20 := by ring
  have hpos : 0 < l1 ^ 2 * l2 ^ 2 := by positivity
  refine (mul_le_mul_iff_of_pos_left hpos).mp ?_
  have heqL : l1 ^ 2 * l2 ^ 2 * (Cw * J ^ 15 * P * (Cz * (1 + Z / l1) * (1 + Z / l2)) ^ 2) =
      Cw * J ^ 15 * Cz ^ 2 * (P * (l1 * (1 + Z / l1)) ^ 2 * (l2 * (1 + Z / l2)) ^ 2) := by
    ring
  have heqR : l1 ^ 2 * l2 ^ 2 * (Cw * Cz ^ 2 * 16 * Z ^ 4 * J ^ 15 * l1 ^ 18 * l2 ^ 18 * l3 ^ 20) =
      Cw * J ^ 15 * Cz ^ 2 * (16 * Z ^ 4 * l1 ^ 20 * l2 ^ 20 * l3 ^ 20) := by ring
  rw [heqL, heqR]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

end Per56

/-- Per-lattice count for the `ℓ^{(56)}` bound: in a rank-`3` sublattice `L ⊆ ℤ^5` with
`λ₁(L) ≤ Z` and `λ₂(L) ≤ Z`, the number of `ℤ`-linearly independent pairs of points of
`L ∩ B(Z)` with `λ₅₆(Γ_{x,y}) ≤ J` is `O(Z⁴ J¹⁵ λ₁¹⁸ λ₂¹⁸ λ₃²⁰)`.

Route: for each pair pick a witness form `a ∈ Γ_{x,y}`, `‖a‖ ≤ J`, `a ∉ vanishOn L`
(`witness_outside`); let `v = (v₁,v₂,v₃)` be three independent vectors of `L` with
`‖v_j‖ ≤ λ_j` (`exists_indep_le_lam`); the witness class `wClass v a` determines the
restriction of the form to `L` (`q44_wclass_determines`), and the number of classes that
occur is `≤ C J¹⁵ ∏_j ‖v_j‖²⁰ ≤ C J¹⁵ λ₁²⁰λ₂²⁰λ₃²⁰` (`witness_class_count`); for each
class the points of `L ∩ B(Z)` on which the form vanishes number at most
`C(1+Z/λ₁)(1+Z/λ₂) ≤ 4C Z²/(λ₁λ₂)` (`latZero_bound`), so the pairs in a fibre number at
most the square of that. -/
theorem q44_perlat_56 :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (Fin 5 → ℤ)), Work.HP.rk L = 3 →
      ∀ (Z J : ℝ), 1 ≤ Z → 1 ≤ J → Work.HP.lam L 1 ≤ Z → Work.HP.lam L 2 ≤ Z →
      (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
          p.1 ∈ L ∧ p.2 ∈ L ∧ Work.HP.eNorm p.1 ≤ Z ∧ Work.HP.eNorm p.2 ≤ Z ∧
          LinearIndependent ℤ ![p.1, p.2] ∧ Work.HP.lam (Work.HP.Gam 4 4 p.1 p.2) 56 ≤ J} :
        Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ) ≤
        C * Z ^ 4 * J ^ 15 * Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20 := by
  classical
  obtain ⟨Cw, hCwpos, hWc⟩ := Work.HP.Q44Child.witness_class_count
  obtain ⟨Cz, hCzpos, hZbc⟩ := Work.HP.Q44Child.latZero_bound
  refine ⟨Cw * Cz ^ 2 * 16, by positivity, ?_⟩
  intro L hL Z J hZ hJ hl1 hl2
  have hl1pos : 0 < Work.HP.lam L 1 := Work.HP.lam_pos L (by norm_num) (by omega)
  have hl2pos : 0 < Work.HP.lam L 2 := Work.HP.lam_pos L (by norm_num) (by omega)
  have hl3pos : 0 < Work.HP.lam L 3 := Work.HP.lam_pos L (by norm_num) (by omega)
  obtain ⟨f, hfL, hfI, hfb⟩ := Work.HP.FM.exists_indep_le_lam L
  let e : Fin 3 → Fin (Work.HP.rk L) := fun j => ⟨j.1, by omega⟩
  let v : Fin 3 → (Fin 5 → ℤ) := fun j => f (e j)
  have he : Function.Injective e := by
    intro a b hab
    exact Fin.ext (by simpa [e] using congrArg Fin.val hab)
  have hvL : ∀ j, v j ∈ L := fun j => hfL (e j)
  have hvI : LinearIndependent ℤ v := by
    have h := hfI.comp e he
    simpa [v, Function.comp_def] using h
  have hvb : ∀ j : Fin 3, Work.HP.eNorm (v j) ≤ Work.HP.lam L (j.1 + 1) := by
    intro j
    have h := hfb (e j)
    simpa [v, e] using h
  -- finiteness of the counted set
  have hSfin : (Per56.pairSet L Z J).Finite :=
    ((Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) Z).prod
        (Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) Z)).subset
      (fun p hp => ⟨hp.2.2.1, hp.2.2.2.1⟩)
  -- a witness form for each counted pair
  have hwit : ∀ p ∈ Per56.pairSet L Z J, ∃ a : Work.HP.Mon 4 4 → ℤ,
      a ∈ Work.HP.Gam 4 4 p.1 p.2 ∧ a ≠ 0 ∧ Work.HP.eNorm a ≤ J ∧
        a ∉ Work.HP.vanishOn L := by
    intro p hp
    exact Work.HP.Q44Child.witness_outside L hL p.1 p.2 hp.1 hp.2.1 J hp.2.2.2.2.2
  let wit : (Fin 5 → ℤ) × (Fin 5 → ℤ) → (Work.HP.Mon 4 4 → ℤ) :=
    fun p => if hp : p ∈ Per56.pairSet L Z J then Classical.choose (hwit p hp) else 0
  have hwit_spec : ∀ p (hp : p ∈ Per56.pairSet L Z J),
      wit p ∈ Work.HP.Gam 4 4 p.1 p.2 ∧ wit p ≠ 0 ∧ Work.HP.eNorm (wit p) ≤ J ∧
        wit p ∉ Work.HP.vanishOn L := by
    intro p hp
    have h : wit p = Classical.choose (hwit p hp) := dif_pos hp
    rw [h]
    exact Classical.choose_spec (hwit p hp)
  let cls : (Fin 5 → ℤ) × (Fin 5 → ℤ) → (Work.HP.Tri4 → ℤ) :=
    fun p => Work.HP.wClass v (wit p)
  -- the range of the class map is small
  have hW := hWc v hvI J hJ
  have himg_sub : cls '' Per56.pairSet L Z J ⊆
      Set.range (fun a : {a : Work.HP.Mon 4 4 → ℤ // Work.HP.eNorm a ≤ J} =>
        Work.HP.wClass v a.1) := by
    rintro c ⟨p, hp, rfl⟩
    exact ⟨⟨wit p, (hwit_spec p hp).2.2.1⟩, rfl⟩
  have himgcard : ((cls '' Per56.pairSet L Z J).ncard : ℝ) ≤
      Cw * J ^ 15 * ∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20 := by
    have h1 : (cls '' Per56.pairSet L Z J).ncard ≤
        (Set.range (fun a : {a : Work.HP.Mon 4 4 → ℤ // Work.HP.eNorm a ≤ J} =>
          Work.HP.wClass v a.1)).ncard := Set.ncard_le_ncard himg_sub hW.1
    exact le_trans (by exact_mod_cast h1) hW.2
  have hvprod : (∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20) ≤
      Work.HP.lam L 1 ^ 20 * Work.HP.lam L 2 ^ 20 * Work.HP.lam L 3 ^ 20 := by
    have h1 : (∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20) ≤
        ∏ j : Fin 3, Work.HP.lam L (j.1 + 1) ^ 20 :=
      Finset.prod_le_prod₀ (fun j _ => by positivity)
        (fun j _ => pow_le_pow_left₀ (Work.HP.eNorm_nonneg (v j)) (hvb j) 20)
    have h2 : (∏ j : Fin 3, Work.HP.lam L (j.1 + 1) ^ 20) =
        Work.HP.lam L 1 ^ 20 * Work.HP.lam L 2 ^ 20 * Work.HP.lam L 3 ^ 20 := by
      rw [Fin.prod_univ_three]
      norm_num
    rw [h2] at h1
    exact h1
  -- each fibre is contained in a square of zeros of a single form
  set Rz : ℝ := Cz * (1 + Z / Work.HP.lam L 1) * (1 + Z / Work.HP.lam L 2) with hRz
  have hRznonneg : 0 ≤ Rz := by
    rw [hRz]
    have h1 : 0 ≤ Z / Work.HP.lam L 1 := div_nonneg (by linarith) (le_of_lt hl1pos)
    have h2 : 0 ≤ Z / Work.HP.lam L 2 := div_nonneg (by linarith) (le_of_lt hl2pos)
    positivity
  have hfibre : ∀ c : Work.HP.Tri4 → ℤ,
      (({p | p ∈ Per56.pairSet L Z J ∧ cls p = c} :
        Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ) ≤ Rz ^ 2 := by
    intro c
    by_cases hne : ({p | p ∈ Per56.pairSet L Z J ∧ cls p = c} :
        Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).Nonempty
    · obtain ⟨p₀, hp₀S, hp₀c⟩ := hne
      have hb_spec := hwit_spec p₀ hp₀S
      have hZbcard : ((Per56.zeroSet L (wit p₀) Z).ncard : ℝ) ≤ Rz := by
        have h := hZbc L hL (wit p₀) hb_spec.2.2.2 Z hZ
        rw [hRz]
        exact h
      have hZbfin : (Per56.zeroSet L (wit p₀) Z).Finite :=
        (Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) Z).subset (fun x hx => hx.2.1)
      have hsub : ({p | p ∈ Per56.pairSet L Z J ∧ cls p = c} :
          Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))) ⊆
          Per56.zeroSet L (wit p₀) Z ×ˢ Per56.zeroSet L (wit p₀) Z := by
        intro p hp
        obtain ⟨hpS, hpc⟩ := hp
        have hclseq : cls p = cls p₀ := hpc.trans hp₀c.symm
        have hcls : Work.HP.wClass v (wit p) = Work.HP.wClass v (wit p₀) := hclseq
        have hdet := Per56.wclassDetermines hL hvI hvL hcls
        have h1 : Work.HP.formEval 4 4 (wit p₀) p.1 = 0 := by
          rw [← hdet p.1 hpS.1]
          exact ((Work.HP.MDBasic.mem_Gam_iff 4 4 p.1 p.2 (wit p)).mp
            (hwit_spec p hpS).1).1
        have h2 : Work.HP.formEval 4 4 (wit p₀) p.2 = 0 := by
          rw [← hdet p.2 hpS.2.1]
          exact ((Work.HP.MDBasic.mem_Gam_iff 4 4 p.1 p.2 (wit p)).mp
            (hwit_spec p hpS).1).2
        exact ⟨⟨hpS.1, hpS.2.2.1, h1⟩, ⟨hpS.2.1, hpS.2.2.2.1, h2⟩⟩
      have hprod := Set.ncard_le_ncard hsub (hZbfin.prod hZbfin)
      calc (({p | p ∈ Per56.pairSet L Z J ∧ cls p = c} :
              Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ)
          ≤ ((Per56.zeroSet L (wit p₀) Z ×ˢ Per56.zeroSet L (wit p₀) Z).ncard : ℝ) := by
            exact_mod_cast hprod
        _ = ((Per56.zeroSet L (wit p₀) Z).ncard : ℝ) *
              ((Per56.zeroSet L (wit p₀) Z).ncard : ℝ) := by
            rw [Set.ncard_prod]
            push_cast
            ring
        _ ≤ Rz * Rz := mul_le_mul hZbcard hZbcard (by positivity) hRznonneg
        _ = Rz ^ 2 := by ring
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
      simp only [Nat.cast_zero]
      positivity
  -- the fibre decomposition of the count
  have htermN : ∀ c : Work.HP.Tri4 → ℤ,
      ({p | p ∈ Per56.pairSet L Z J ∧ cls p = c} :
        Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard =
        (hSfin.toFinset.filter (fun p => cls p = c)).card := by
    intro c
    have hfin : ({p | p ∈ Per56.pairSet L Z J ∧ cls p = c} :
        Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).Finite :=
      hSfin.subset (fun p hp => hp.1)
    rw [Set.ncard_eq_toFinset_card _ hfin]
    congr 1
    ext p
    simp [Set.Finite.mem_toFinset, Finset.mem_filter]
  have hSdecomp : ((Per56.pairSet L Z J).ncard : ℝ) =
      ∑ c ∈ (hSfin.toFinset.image cls),
        (({p | p ∈ Per56.pairSet L Z J ∧ cls p = c} :
          Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ) := by
    have hN : (Per56.pairSet L Z J).ncard =
        ∑ c ∈ (hSfin.toFinset.image cls),
          ({p | p ∈ Per56.pairSet L Z J ∧ cls p = c} :
            Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard := by
      rw [Set.ncard_eq_toFinset_card _ hSfin]
      rw [Finset.card_eq_sum_card_fiberwise (f := cls) (s := hSfin.toFinset)
        (t := hSfin.toFinset.image cls) (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
      exact Finset.sum_congr rfl (fun c _ => (htermN c).symm)
    rw [hN, Nat.cast_sum]
  have hbound1 : ((Per56.pairSet L Z J).ncard : ℝ) ≤
      ((hSfin.toFinset.image cls).card : ℝ) * Rz ^ 2 := by
    rw [hSdecomp]
    calc ∑ c ∈ (hSfin.toFinset.image cls),
            (({p | p ∈ Per56.pairSet L Z J ∧ cls p = c} :
              Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ)
        ≤ ∑ _c ∈ (hSfin.toFinset.image cls), Rz ^ 2 :=
          Finset.sum_le_sum (fun c _ => hfibre c)
      _ = ((hSfin.toFinset.image cls).card : ℝ) * Rz ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have himgcard' : ((hSfin.toFinset.image cls).card : ℝ) ≤
      Cw * J ^ 15 * ∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20 := by
    have h1 : (hSfin.toFinset.image cls).card ≤ (cls '' Per56.pairSet L Z J).ncard := by
      rw [← Set.ncard_coe_finset (s := hSfin.toFinset.image cls)]
      refine Set.ncard_le_ncard ?_ (hW.1.subset himg_sub)
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_image] at hc
      obtain ⟨p, hp, rfl⟩ := hc
      exact ⟨p, hSfin.mem_toFinset.mp hp, rfl⟩
    exact le_trans (by exact_mod_cast h1) himgcard
  have hstep : ((Per56.pairSet L Z J).ncard : ℝ) ≤
      (Cw * J ^ 15 * ∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20) * Rz ^ 2 := by
    calc ((Per56.pairSet L Z J).ncard : ℝ)
        ≤ ((hSfin.toFinset.image cls).card : ℝ) * Rz ^ 2 := hbound1
      _ ≤ (Cw * J ^ 15 * ∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20) * Rz ^ 2 :=
          mul_le_mul_of_nonneg_right himgcard' (by positivity)
  have hfin_bound : (Cw * J ^ 15 * ∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20) * Rz ^ 2 ≤
      Cw * Cz ^ 2 * 16 * Z ^ 4 * J ^ 15 * Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 *
        Work.HP.lam L 3 ^ 20 := by
    have h2 := Per56.perlatArith Cw Cz Z J (Work.HP.lam L 1) (Work.HP.lam L 2)
      (Work.HP.lam L 3) (∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20) hCwpos hCzpos
      (by linarith) (by linarith) hl1pos hl2pos hl3pos hl1 hl2 hvprod
    simpa [hRz] using h2
  calc (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
          p.1 ∈ L ∧ p.2 ∈ L ∧ Work.HP.eNorm p.1 ≤ Z ∧ Work.HP.eNorm p.2 ≤ Z ∧
          LinearIndependent ℤ ![p.1, p.2] ∧ Work.HP.lam (Work.HP.Gam 4 4 p.1 p.2) 56 ≤ J} :
        Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ)
      = ((Per56.pairSet L Z J).ncard : ℝ) := rfl
    _ ≤ (Cw * J ^ 15 * ∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20) * Rz ^ 2 := hstep
    _ ≤ Cw * Cz ^ 2 * 16 * Z ^ 4 * J ^ 15 * Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 *
          Work.HP.lam L 3 ^ 20 := hfin_bound

end Work.HP.MDEstimates

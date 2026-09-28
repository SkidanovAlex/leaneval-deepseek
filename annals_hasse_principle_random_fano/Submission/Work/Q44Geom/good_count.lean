import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.Basic
import Submission.Work.Q44Geom.sat_span
import Submission.Work.Q44Geom.ratSpan_finrank
import Submission.Work.Q44Geom.vanish_ratSpan
import Submission.Work.Q44Geom.rat_coerce_linIndep
import Submission.Work.Q44Geom.zero_count
import Submission.Work.Q44Geom.formOf_eval
import Submission.Work.Q44Geom.planes44
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.Q44Geom.ncard_le_mul_image
import Submission.Work.Q44Geom.ncard_le_planeSet_ncard

/-!
# `Work.Q44Geom.good_count`

The number of `L ∈ Sset c s` admitting a *good pair* is `≪ s 0 ^ 4 * s 1 ^ 4`, with a
constant uniform in `c` and `s`.

The proof groups the lattices of `Sset c s` carrying a good pair by the *canonical* good pair
(chosen with `Classical.choose` out of `goodPair c s L`) and uses two ingredients:

* `Work.Q44Geom.planes44`: for a pair `(b₁,b₂)` satisfying the hypotheses of that lemma, the
  number of isotropic `3`-planes containing both is bounded by an absolute constant.  Since
  `L ↦ ratSpan L` is injective on primitive lattices, this bounds the number of lattices per
  fibre (`ncard_le_planeSet_ncard`).
* `Work.Q44Geom.zero_count`: the number of integral zeros of a nonzero quartic form of norm at
  most `T` is `≪ T ^ 4`; applied to the two coordinates of the canonical pair it bounds the
  number of fibres.
-/

set_option autoImplicit false
noncomputable section

open MvPolynomial
open Classical

namespace Work.Q44Geom

/-- The canonical pair extracted from a proof of `goodPair c s L`. -/
def cpr (c : Work.HP.Mon 4 4 → ℤ) (s : Fin 3 → ℝ) (L : Submodule ℤ (Fin 5 → ℤ))
    (h : goodPair c s L) : (Fin 5 → ℤ) × (Fin 5 → ℤ) :=
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

/-- Specification of the canonical pair. -/
lemma cpr_spec {c : Work.HP.Mon 4 4 → ℤ} {s : Fin 3 → ℝ} {L : Submodule ℤ (Fin 5 → ℤ)}
    (h : goodPair c s L) :
    (cpr c s L h).1 ∈ L ∧ (cpr c s L h).2 ∈ L ∧
      LinearIndependent ℤ ![(cpr c s L h).1, (cpr c s L h).2] ∧
      Work.HP.eNorm (cpr c s L h).1 ≤ s 0 ∧ Work.HP.eNorm (cpr c s L h).2 ≤ s 1 ∧
      (Work.Q44Geom.toRatLM (cpr c s L h).1 ∉ invSub (f44 c) ∨
        Work.Q44Geom.toRatLM (cpr c s L h).2 ∉ invSub (f44 c)) :=
  Classical.choose_spec (Classical.choose_spec h)

/-- The canonical-pair map, totalised by an arbitrary default outside `G`. -/
def cprFun (c : Work.HP.Mon 4 4 → ℤ) (s : Fin 3 → ℝ)
    {G : Set (Submodule ℤ (Fin 5 → ℤ))} (hg : ∀ L ∈ G, goodPair c s L)
    (L : Submodule ℤ (Fin 5 → ℤ)) : (Fin 5 → ℤ) × (Fin 5 → ℤ) :=
  if h : L ∈ G then cpr c s L (hg L h) else (0, 0)

lemma cprFun_of_mem {c : Work.HP.Mon 4 4 → ℤ} {s : Fin 3 → ℝ}
    {G : Set (Submodule ℤ (Fin 5 → ℤ))} (hg : ∀ L ∈ G, goodPair c s L)
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ∈ G) :
    cprFun c s hg L = cpr c s L (hg L hL) := by
  rw [cprFun]
  exact dite_eq_left hL

/-- The set of isotropic `3`-planes of `ℚ⁵` containing `toRatLM b₁` and `toRatLM b₂`. -/
def planeSet (c : Work.HP.Mon 4 4 → ℤ) (b₁ b₂ : Fin 5 → ℤ) : Set (Submodule ℚ (Fin 5 → ℚ)) :=
  {P | Module.finrank ℚ P = 3 ∧ Work.Q44Geom.toRatLM b₁ ∈ P ∧
    Work.Q44Geom.toRatLM b₂ ∈ P ∧ ∀ x ∈ P, MvPolynomial.eval x (f44 c) = 0}

/-- The integral zeros of `f44 c` of Euclidean norm at most `T`. -/
def zerSet (c : Work.HP.Mon 4 4 → ℤ) (T : ℝ) : Set (Fin 5 → ℤ) :=
  {x | Work.HP.eNorm x ≤ T ∧ MvPolynomial.eval (Work.Q44Geom.toRatLM x) (f44 c) = 0}

/-- `f44 c` is a quartic form, hence of total degree at most `4`. -/
lemma f44_totalDegree_le (c : Work.HP.Mon 4 4 → ℤ) : (f44 c).totalDegree ≤ 4 := by
  have hhom : (f44 c).IsHomogeneous 4 := by
    rw [f44, Work.HP.formOf]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun m _ =>
      MvPolynomial.isHomogeneous_monomial (c m : ℚ) (Work.HP.Mon_degree_toFinsupp m)
  exact hhom.totalDegree_le

/-- The first vector of a `ℤ`-linearly independent pair is nonzero. -/
lemma pair_fst_ne_zero {b₁ b₂ : Fin 5 → ℤ} (h : LinearIndependent ℤ ![b₁, b₂]) : b₁ ≠ 0 := by
  intro h0
  have hsum : (∑ j : Fin 2, (![1, 0] : Fin 2 → ℤ) j • ![b₁, b₂] j) = 0 := by
    rw [Fin.sum_univ_two]
    simp [h0]
  have h1 : (1 : ℤ) = 0 := by
    simpa using Fintype.linearIndependent_iff.mp h ![1, 0] hsum 0
  exact absurd h1 (by norm_num)

/-- The second vector of a `ℤ`-linearly independent pair is nonzero. -/
lemma pair_snd_ne_zero {b₁ b₂ : Fin 5 → ℤ} (h : LinearIndependent ℤ ![b₁, b₂]) : b₂ ≠ 0 := by
  intro h0
  have hsum : (∑ j : Fin 2, (![0, 1] : Fin 2 → ℤ) j • ![b₁, b₂] j) = 0 := by
    rw [Fin.sum_univ_two]
    simp [h0]
  have h1 : (1 : ℤ) = 0 := by
    simpa using Fintype.linearIndependent_iff.mp h ![0, 1] hsum 1
  exact absurd h1 (by norm_num)

/-- An integral vector whose rational image vanishes is zero, hence a nonzero integral vector
has a nonzero rational image. -/
lemma toRatLM_ne_zero {b : Fin 5 → ℤ} (h : b ≠ 0) : Work.Q44Geom.toRatLM b ≠ 0 := by
  intro h0
  refine h (funext fun i => ?_)
  have hi : ((b i : ℤ) : ℚ) = 0 := congrFun h0 i
  exact_mod_cast hi

/-- **`planes44` for integral data**: for a pair `(b₁,b₂)` of nonzero integral vectors which is
`ℚ`-independent, on which `f44 c` vanishes, and which is not contained in the invariance
subspace of `f44 c`, the number of isotropic `3`-planes through them is bounded by a constant
depending only on `c`. -/
lemma planeSet_finite_and_ncard_le :
    ∃ K : ℕ, 0 < K ∧ ∀ (c : Work.HP.Mon 4 4 → ℤ) (b₁ b₂ : Fin 5 → ℤ),
      Work.HP.formOf 4 4 c ≠ 0 → Irreducible (Work.HP.formOf 4 4 c) → b₁ ≠ 0 → b₂ ≠ 0 →
      LinearIndependent ℚ ![Work.Q44Geom.toRatLM b₁, Work.Q44Geom.toRatLM b₂] →
      MvPolynomial.eval (Work.Q44Geom.toRatLM b₁) (f44 c) = 0 →
      MvPolynomial.eval (Work.Q44Geom.toRatLM b₂) (f44 c) = 0 →
      (¬ ∀ (a b : ℚ) (x : Fin 5 → ℚ),
        MvPolynomial.eval (x + a • Work.Q44Geom.toRatLM b₁ + b • Work.Q44Geom.toRatLM b₂)
          (f44 c) = MvPolynomial.eval x (f44 c)) →
      (planeSet c b₁ b₂).Finite ∧ (planeSet c b₁ b₂).ncard ≤ K := by
  obtain ⟨Cp, hCp0, hCp⟩ := planes44
  have hceil : 0 < ⌈Cp⌉₊ := Nat.ceil_pos.mpr hCp0
  refine ⟨⌈Cp⌉₊, hceil, ?_⟩
  intro c b₁ b₂ hc0 hcirr hb₁ hb₂ hli hv₁ hv₂ hni
  have h := hCp c hc0 hcirr (Work.Q44Geom.toRatLM b₁) (Work.Q44Geom.toRatLM b₂)
    (toRatLM_ne_zero hb₁) (toRatLM_ne_zero hb₂) hli hv₁ hv₂ hni (planeSet c b₁ b₂)
    (fun P hP => hP)
  refine ⟨h.1, ?_⟩
  have h2 : ((planeSet c b₁ b₂).ncard : ℝ) ≤ (⌈Cp⌉₊ : ℝ) := le_trans h.2 (Nat.le_ceil Cp)
  exact_mod_cast h2

/-- The two-variable zero set of `f44 c` is contained in the ball, hence finite. -/
lemma zerSet_finite (c : Work.HP.Mon 4 4 → ℤ) (T : ℝ) : (zerSet c T).Finite :=
  (Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) T).subset fun x hx => hx.1

/-- Vanishing at a lattice point of `L ∈ Sset c s` gives vanishing of the rational form. -/
lemma zerSet_mem_of_mem_Sset {c : Work.HP.Mon 4 4 → ℤ} {s : Fin 3 → ℝ}
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ∈ Sset c s) {v : Fin 5 → ℤ} (hv : v ∈ L) :
    v ∈ zerSet c (Work.HP.eNorm v) := by
  refine ⟨le_rfl, ?_⟩
  have hvanish : c ∈ Work.HP.vanishOn L := hL.2.2.2
  have h := (Work.HP.mem_vanishOn (L := L) (a := c)).mp hvanish ⟨v, hv⟩
  rw [Work.Q44Geom.formOf_eval c v, h, Int.cast_zero]

theorem good_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Work.HP.Mon 4 4 → ℤ), Work.HP.formOf 4 4 c ≠ 0 →
      Irreducible (Work.HP.formOf 4 4 c) → ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 →
      (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ Work.Q44Geom.Sset c s ∧
        Work.Q44Geom.goodPair c s L} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ C * (s 0) ^ 4 * (s 1) ^ 4 := by
  obtain ⟨C0, hC00, hC0⟩ := zero_count
  obtain ⟨Kp, hKppos, hKp⟩ := planeSet_finite_and_ncard_le
  have hKp0 : (0 : ℝ) < (Kp : ℝ) := by exact_mod_cast hKppos
  refine ⟨(Kp : ℝ) * C0 * C0, by positivity, ?_⟩
  intro c hc0 hcirr s hs0 hs01
  have hs1 : 1 ≤ s 1 := le_trans hs0 hs01
  have hs0' : (0 : ℝ) ≤ s 0 := le_trans zero_le_one hs0
  have hs1' : (0 : ℝ) ≤ s 1 := le_trans zero_le_one hs1
  have hKpR : (0 : ℝ) ≤ (Kp : ℝ) := Nat.cast_nonneg _
  have hC0R : (0 : ℝ) ≤ C0 := le_of_lt hC00
  set G : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | L ∈ Sset c s ∧ goodPair c s L} with hG
  have hgoodG : ∀ L ∈ G, goodPair c s L := by
    intro L hL
    rw [hG] at hL
    exact hL.2
  have hSset : ∀ L ∈ G, L ∈ Sset c s := by
    intro L hL
    rw [hG] at hL
    exact hL.1
  by_cases hGfin : G.Finite
  · -- main case: `G` is finite, count the fibres of the canonical-pair map
    have hfib : ∀ p : (Fin 5 → ℤ) × (Fin 5 → ℤ),
        (G ∩ (cprFun c s hgoodG) ⁻¹' {p}).ncard ≤ Kp := by
      intro p
      by_cases hp : p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
          LinearIndependent ℚ ![Work.Q44Geom.toRatLM p.1, Work.Q44Geom.toRatLM p.2] ∧
          MvPolynomial.eval (Work.Q44Geom.toRatLM p.1) (f44 c) = 0 ∧
          MvPolynomial.eval (Work.Q44Geom.toRatLM p.2) (f44 c) = 0 ∧
          (¬ ∀ (a b : ℚ) (x : Fin 5 → ℚ),
            MvPolynomial.eval (x + a • Work.Q44Geom.toRatLM p.1 + b • Work.Q44Geom.toRatLM p.2)
              (f44 c) = MvPolynomial.eval x (f44 c))
      · obtain ⟨hp1, hp2, hli, hv1, hv2, hni⟩ := hp
        obtain ⟨hPfin, hPncard⟩ := hKp c p.1 p.2 hc0 hcirr hp1 hp2 hli hv1 hv2 hni
        refine le_trans (ncard_le_planeSet_ncard c s p.1 p.2
          (G ∩ (cprFun c s hgoodG) ⁻¹' {p}) ?_ hPfin) hPncard
        intro L hL
        obtain ⟨hLG, hφL⟩ := hL
        have hpair := cpr_spec (c := c) (s := s) (L := L) (hgoodG L hLG)
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hφL
        rw [cprFun_of_mem (c := c) (s := s) hgoodG hLG] at hφL
        obtain rfl : p = cpr c s L (hgoodG L hLG) := hφL.symm
        exact ⟨hSset L hLG, hpair.1, hpair.2.1⟩
      · -- the fibre is empty: the canonical pair of any member satisfies all the conditions
        have hempty : G ∩ (cprFun c s hgoodG) ⁻¹' {p} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro L ⟨hLG, hφL⟩
          have hpair := cpr_spec (c := c) (s := s) (L := L) (hgoodG L hLG)
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hφL
          rw [cprFun_of_mem (c := c) (s := s) hgoodG hLG] at hφL
          obtain rfl : p = cpr c s L (hgoodG L hLG) := hφL.symm
          refine hp ⟨pair_fst_ne_zero hpair.2.2.1, pair_snd_ne_zero hpair.2.2.1,
            Work.Q44Geom.rat_coerce_linIndep _ _ hpair.2.2.1, ?_, ?_, ?_⟩
          · exact (zerSet_mem_of_mem_Sset (hSset L hLG) hpair.1).2
          · exact (zerSet_mem_of_mem_Sset (hSset L hLG) hpair.2.1).2
          · intro h
            obtain ⟨h1, h2⟩ := inv_of_inv_pair (f := f44 c) h
            rcases hpair.2.2.2.2.2 with hn | hn
            · exact hn h1
            · exact hn h2
        rw [hempty]
        simp
    -- the fibres bound `#G` by the number of canonical pairs
    have hGbound : G.ncard ≤ Kp * ((cprFun c s hgoodG) '' G).ncard :=
      ncard_le_mul_image hGfin (cprFun c s hgoodG) Kp hfib
    -- every canonical pair consists of two zeros of `f44 c` of norm at most `s 0`, `s 1`
    have hI_sub : (cprFun c s hgoodG) '' G ⊆ zerSet c (s 0) ×ˢ zerSet c (s 1) := by
      rintro p ⟨L, hLG, rfl⟩
      have hpair := cpr_spec (c := c) (s := s) (L := L) (hgoodG L hLG)
      rw [cprFun_of_mem (c := c) (s := s) hgoodG hLG]
      exact ⟨⟨hpair.2.2.2.1, (zerSet_mem_of_mem_Sset (hSset L hLG) hpair.1).2⟩,
        ⟨hpair.2.2.2.2.1, (zerSet_mem_of_mem_Sset (hSset L hLG) hpair.2.1).2⟩⟩
    have hI_le : ((cprFun c s hgoodG) '' G).ncard ≤
        (zerSet c (s 0) ×ˢ zerSet c (s 1)).ncard :=
      Set.ncard_le_ncard hI_sub ((zerSet_finite c (s 0)).prod (zerSet_finite c (s 1)))
    have hZ0 : ((zerSet c (s 0)).ncard : ℝ) ≤ C0 * (s 0) ^ 4 :=
      hC0 (f44 c) hc0 (f44_totalDegree_le c) (s 0) hs0
    have hZ1 : ((zerSet c (s 1)).ncard : ℝ) ≤ C0 * (s 1) ^ 4 :=
      hC0 (f44 c) hc0 (f44_totalDegree_le c) (s 1) hs1
    have hZ0' : (0 : ℝ) ≤ ((zerSet c (s 0)).ncard : ℝ) := Nat.cast_nonneg _
    have hZ1' : (0 : ℝ) ≤ ((zerSet c (s 1)).ncard : ℝ) := Nat.cast_nonneg _
    have hstep : ((zerSet c (s 0)).ncard : ℝ) * ((zerSet c (s 1)).ncard : ℝ)
        ≤ (C0 * (s 0) ^ 4) * (C0 * (s 1) ^ 4) :=
      mul_le_mul hZ0 hZ1 hZ1' (mul_nonneg hC0R (pow_nonneg hs0' 4))
    calc (G.ncard : ℝ)
        ≤ (Kp : ℝ) * (((cprFun c s hgoodG) '' G).ncard : ℝ) := by exact_mod_cast hGbound
      _ ≤ (Kp : ℝ) * ((zerSet c (s 0) ×ˢ zerSet c (s 1)).ncard : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hI_le) hKpR
      _ = (Kp : ℝ) * (((zerSet c (s 0)).ncard : ℝ) * ((zerSet c (s 1)).ncard : ℝ)) := by
          rw [Set.ncard_prod]; push_cast; ring
      _ ≤ (Kp : ℝ) * ((C0 * (s 0) ^ 4) * (C0 * (s 1) ^ 4)) :=
          mul_le_mul_of_nonneg_left hstep hKpR
      _ = (Kp : ℝ) * C0 * C0 * (s 0) ^ 4 * (s 1) ^ 4 := by ring
  · -- `G` is infinite: its cardinality is `0`, and the right-hand side is nonnegative
    have hn : G.ncard = 0 := (show G.Infinite from hGfin).ncard
    rw [hn, Nat.cast_zero]
    have h1 : (0 : ℝ) ≤ (Kp : ℝ) * C0 * C0 * (s 0) ^ 4 * (s 1) ^ 4 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hKpR hC0R) hC0R)
        (pow_nonneg hs0' 4)) (pow_nonneg hs1' 4)
    linarith

end Work.Q44Geom

import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.MDEstimates.polarQuadFacts
import Submission.Work.HP.MDEstimates.coneInRad
import Submission.Work.HP.MDEstimates.detL_le_prod_lam
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.ballCount_le_pow_rk
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.Sig2.Tset_finite
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.sat_span
import Submission.Work.Q44Geom.ratSpan_finrank
import Submission.Work.Q44Geom.Basic
import Submission.Work.Q44Geom.zero_count
import Submission.Work.Q44Geom.ncard_le_mul_image
import Submission.Work.Q44Geom.rat_coerce_linIndep
import Submission.Work.HP.Q44Main.QuadCount.radSub_mem_iff
import Submission.Work.HP.Q44Main.QuadCount.planesNotRadFinset
import Submission.Work.HP.Q44Main.QuadCount.radLatSub_rank
import Submission.Work.HP.Q44Main.QuadCount.finrank_radSub_le_three
import Submission.Work.HP.Q44Main.QuadCount.superlattice_window_count

/-!
# The quadric lattice count `Work.HP.Q44Main.latS_quad_count`

For a nonzero homogeneous quadratic form `Q` in five variables without a linear factor, the
number of primitive rank-`3` sublattices `L ⊆ ℤ^5` on which `Q` vanishes identically and whose
successive minima satisfy `λ_{j+1}(L) ≤ s j` is `≪ (s 0 * s 1 * s 2) ^ 3`, uniformly in `Q`.

The proof groups the lattices by the canonical pair `(cpair Q s L)` of two short independent
lattice vectors and splits into three cases `SA`, `SB`, `SC` according to which members of the
pair lie in the radical of the polar form of `Q`.  The case `3 ≤ finrank (radSub Q)` is settled
separately using `coneInRad`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section
open MvPolynomial Finset
open Classical

namespace Work.HP.Q44Main

open Work.HP.MDEstimates

/-! ## Elementary arithmetic -/

lemma sq_four_le (s : Fin 3 → ℝ) (hs0 : 1 ≤ s 0) (hs01 : s 0 ≤ s 1) (hs12 : s 1 ≤ s 2) :
    s 0 ^ 4 * s 1 ^ 4 ≤ (s 0 * s 1 * s 2) ^ 3 := by
  have h1 : (0 : ℝ) < s 0 := lt_of_lt_of_le zero_lt_one hs0
  have h2 : (1 : ℝ) ≤ s 1 := le_trans hs0 hs01
  have h3 : (1 : ℝ) ≤ s 2 := le_trans h2 hs12
  have hle : s 0 * s 1 ≤ s 2 ^ 3 := by nlinarith [h1, h2, h3, sq_nonneg (s 2)]
  calc s 0 ^ 4 * s 1 ^ 4 = (s 0 * s 1) ^ 3 * (s 0 * s 1) := by ring
    _ ≤ (s 0 * s 1) ^ 3 * s 2 ^ 3 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (s 0 * s 1 * s 2) ^ 3 := by ring

lemma sq_two_four_le (s : Fin 3 → ℝ) (hs0 : 1 ≤ s 0) (hs01 : s 0 ≤ s 1) (hs12 : s 1 ≤ s 2) :
    s 0 ^ 2 * s 1 ^ 4 ≤ (s 0 * s 1 * s 2) ^ 3 := by
  have h4 := sq_four_le s hs0 hs01 hs12
  have h0 : (1 : ℝ) ≤ s 0 ^ 2 := one_le_pow₀ hs0
  have h1 : (0 : ℝ) ≤ s 1 ^ 4 := by positivity
  have h2 : s 0 ^ 2 * s 1 ^ 4 ≤ s 0 ^ 4 * s 1 ^ 4 := by
    have h3 : s 0 ^ 2 ≤ s 0 ^ 4 := by
      calc s 0 ^ 2 = s 0 ^ 2 * 1 := by ring
        _ ≤ s 0 ^ 2 * s 0 ^ 2 := mul_le_mul_of_nonneg_left h0 (by positivity)
        _ = s 0 ^ 4 := by ring
    exact mul_le_mul_of_nonneg_right h3 h1
  linarith

lemma one_le_prod (s : Fin 3 → ℝ) (hs0 : 1 ≤ s 0) (hs01 : s 0 ≤ s 1) (hs12 : s 1 ≤ s 2) :
    1 ≤ s 0 * s 1 * s 2 := by
  have h2 : (1 : ℝ) ≤ s 1 := le_trans hs0 hs01
  have h3 : (1 : ℝ) ≤ s 2 := le_trans h2 hs12
  have h4 : (1 : ℝ) ≤ s 0 * s 1 := by nlinarith [hs0, h2]
  have h5 : (1 : ℝ) ≤ (s 0 * s 1) * s 2 := by nlinarith [h4, h3]
  exact h5

/-! ## The integral radical -/

lemma isPrimLat_radLatSub (Q : MvPolynomial (Fin 5) ℚ) :
    Work.HP.IsPrimLat (radLatSub Q) := by
  intro v m hm hmv
  have h1 : Work.Q44Geom.toRatLM (m • v) ∈ radSub Q := hmv
  have h2 : ((m : ℚ)) ≠ 0 := by exact_mod_cast hm
  have h3 : ((m : ℚ))⁻¹ • Work.Q44Geom.toRatLM (m • v) ∈ radSub Q :=
    Submodule.smul_mem _ _ h1
  have h4 : Work.Q44Geom.toRatLM (m • v) = (m : ℚ) • Work.Q44Geom.toRatLM v := by
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ m (Work.Q44Geom.toRatLM v)]
  rw [h4] at h3
  rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at h3

lemma eval_zero_of_mem_radLatSub (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    {x : Fin 5 → ℤ} (hx : x ∈ radLatSub Q) :
    MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0 := by
  have h1 : Work.Q44Geom.toRatLM x ∈ radQ Q :=
    (Work.HP.Q44Main.QuadCount.radSub_mem_iff Q hQ _).mp hx
  have h2 : polQ Q (Work.Q44Geom.toRatLM x) (Work.Q44Geom.toRatLM x) = 0 := h1 _
  rw [← h2]
  exact ((polarQuadFacts Q hQ).2.2.2.1 _).symm

lemma eval_zero_of_mem_ratSpan (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    {L : Submodule ℤ (Fin 5 → ℤ)}
    (h : ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0)
    {v : Fin 5 → ℚ} (hv : v ∈ Work.Q44Geom.ratSpan L) : MvPolynomial.eval v Q = 0 := by
  obtain ⟨n, hn, hmem⟩ := (Work.Q44Geom.mem_ratSpan_iff' L v).mp hv
  obtain ⟨w, hwL, hw⟩ := Submodule.mem_map.mp hmem
  have h0 : MvPolynomial.eval (fun i => (w i : ℚ)) Q = 0 := h w hwL
  have h1 : MvPolynomial.eval (n • v) Q = 0 := by rw [← hw]; exact h0
  have h2 : MvPolynomial.eval ((n : ℚ) • v) Q = (n : ℚ) ^ 2 * MvPolynomial.eval v Q :=
    (polarQuadFacts Q hQ).2.2.2.2.1 (n : ℚ) v
  rw [← Int.cast_smul_eq_zsmul ℚ n v] at h1
  rw [h2] at h1
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 (by exact_mod_cast hn))

lemma eq_of_ratSpan_eq {L L' : Submodule ℤ (Fin 5 → ℤ)} (hL : Work.HP.IsPrimLat L)
    (hL' : Work.HP.IsPrimLat L') (h : Work.Q44Geom.ratSpan L = Work.Q44Geom.ratSpan L') :
    L = L' := by
  ext v
  rw [Work.Q44Geom.sat_span L hL v, Work.Q44Geom.sat_span L' hL' v, h]

/-- The `ℚ`-span of the `ℤ`-span of a family of integral vectors is their `ℚ`-span. -/
lemma ratSpan_span_pair (b₁ b₂ : Fin 5 → ℤ) :
    Work.Q44Geom.ratSpan (Submodule.span ℤ ({b₁, b₂} : Set (Fin 5 → ℤ))) =
      Submodule.span ℚ ({Work.Q44Geom.toRatLM b₁, Work.Q44Geom.toRatLM b₂} :
        Set (Fin 5 → ℚ)) := by
  rw [Work.Q44Geom.ratSpan_eq, Submodule.map_span, Submodule.span_span_of_tower ℤ]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy | hy, rfl⟩
    · exact Or.inl (by rw [hy])
    · exact Or.inr (by rw [hy])
  · rintro (hx | hx)
    · exact ⟨b₁, Or.inl rfl, hx.symm⟩
    · exact ⟨b₂, Or.inr rfl, hx.symm⟩

/-- The `ℚ`-span of two linearly independent vectors is `2`-dimensional. -/
lemma finrank_span_pair {a b : Fin 5 → ℚ} (h : LinearIndependent ℚ ![a, b]) :
    Module.finrank ℚ (Submodule.span ℚ ({a, b} : Set (Fin 5 → ℚ))) = 2 := by
  have hrange : (Set.range ![a, b] : Set (Fin 5 → ℚ)) = {a, b} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · exact ⟨0, by simp [hz]⟩
      · exact ⟨1, by simp [hz]⟩
  rw [← hrange, finrank_span_eq_card h]
  simp

/-! ## The canonical short pair -/

lemma exists_short_pair_canon (Q : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ)
    (L : Submodule ℤ (Fin 5 → ℤ)) (hL : L ∈ Qset Q s) :
    ∃ b₁ b₂ : Fin 5 → ℤ, b₁ ∈ L ∧ b₂ ∈ L ∧ LinearIndependent ℤ ![b₁, b₂] ∧
      Work.HP.eNorm b₁ ≤ s 0 ∧ Work.HP.eNorm b₂ ≤ s 1 :=
  Work.Q44Geom.exists_pair_short L hL.2.1 s hL.2.2.1

def cpair (Q : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ)
    (L : Submodule ℤ (Fin 5 → ℤ)) : (Fin 5 → ℤ) × (Fin 5 → ℤ) :=
  if h : L ∈ Qset Q s then
    (Classical.choose (exists_short_pair_canon Q s L h),
     Classical.choose (Classical.choose_spec (exists_short_pair_canon Q s L h)))
  else (0, 0)

lemma cpair_spec {Q : MvPolynomial (Fin 5) ℚ} {s : Fin 3 → ℝ}
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ∈ Qset Q s) :
    (cpair Q s L).1 ∈ L ∧ (cpair Q s L).2 ∈ L ∧
      LinearIndependent ℤ ![(cpair Q s L).1, (cpair Q s L).2] ∧
      Work.HP.eNorm (cpair Q s L).1 ≤ s 0 ∧ Work.HP.eNorm (cpair Q s L).2 ≤ s 1 := by
  rw [cpair, dif_pos hL]
  exact Classical.choose_spec (Classical.choose_spec (exists_short_pair_canon Q s L hL))

def SA (Q : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | L ∈ Qset Q s ∧ Work.Q44Geom.toRatLM (cpair Q s L).1 ∉ radSub Q}

def SB (Q : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | L ∈ Qset Q s ∧ Work.Q44Geom.toRatLM (cpair Q s L).1 ∈ radSub Q ∧
    Work.Q44Geom.toRatLM (cpair Q s L).2 ∈ radSub Q}

def SC (Q : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | L ∈ Qset Q s ∧ Work.Q44Geom.toRatLM (cpair Q s L).1 ∈ radSub Q ∧
    Work.Q44Geom.toRatLM (cpair Q s L).2 ∉ radSub Q}

lemma Qset_subset_cases (Q : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ) :
    Qset Q s ⊆ SA Q s ∪ (SB Q s ∪ SC Q s) := by
  intro L hL
  by_cases h1 : Work.Q44Geom.toRatLM (cpair Q s L).1 ∈ radSub Q
  · by_cases h2 : Work.Q44Geom.toRatLM (cpair Q s L).2 ∈ radSub Q
    · exact Or.inr (Or.inl ⟨hL, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨hL, h1, h2⟩)
  · exact Or.inl ⟨hL, h1⟩

/-! ## The fibre bounds for the cases `SA` and `SC` -/

lemma fiber_SA_le_two (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hnolf : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False)
    (s : Fin 3 → ℝ) (p : (Fin 5 → ℤ) × (Fin 5 → ℤ))
    (hp : Work.Q44Geom.toRatLM p.1 ∉ radSub Q)
    (hpe : MvPolynomial.eval (fun i => (p.1 i : ℚ)) Q = 0) :
    (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ SA Q s ∧ cpair Q s L = p} :
      Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ 2 := by
  classical
  obtain ⟨S, hScard, hS⟩ :=
    Work.HP.Q44Main.QuadCount.planesNotRadFinset Q hQ hQ0 hnolf hpe
      (fun hc => hp ((Work.HP.Q44Main.QuadCount.radSub_mem_iff Q hQ
        (Work.Q44Geom.toRatLM p.1)).mpr hc))
  set G : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | L ∈ SA Q s ∧ cpair Q s L = p} with hGdef
  have hinj : Set.InjOn (fun L : Submodule ℤ (Fin 5 → ℤ) => Work.Q44Geom.ratSpan L) G := by
    intro L hL L' hL' h
    exact eq_of_ratSpan_eq hL.1.1.1 hL'.1.1.1 h
  have hmaps : ∀ L ∈ G, Work.Q44Geom.ratSpan L ∈ S := by
    intro L hL
    obtain ⟨hLs, hcp⟩ := hL
    obtain ⟨hQset, -⟩ := hLs
    refine hS _ (Work.Q44Geom.ratSpan_finrank L hQset.2.1) ?_ ?_
    · rw [← hcp]
      exact (Work.Q44Geom.sat_span L hQset.1 (cpair Q s L).1).mp (cpair_spec hQset).1
    · intro v hv
      exact eval_zero_of_mem_ratSpan Q hQ (fun x hx => hQset.2.2.2 x hx) hv
  have hstep : G.ncard ≤ S.card := by
    have h1 := Set.ncard_le_ncard_of_injOn
      (fun L : Submodule ℤ (Fin 5 → ℤ) => Work.Q44Geom.ratSpan L) hmaps hinj S.finite_toSet
    rwa [Set.ncard_coe_finset] at h1
  have h2 : G.ncard ≤ 2 := le_trans hstep hScard
  exact_mod_cast h2

lemma fiber_SC_le_two (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hnolf : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False)
    (s : Fin 3 → ℝ) (p : (Fin 5 → ℤ) × (Fin 5 → ℤ))
    (hp : Work.Q44Geom.toRatLM p.2 ∉ radSub Q)
    (hpe : MvPolynomial.eval (fun i => (p.2 i : ℚ)) Q = 0) :
    (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ SC Q s ∧ cpair Q s L = p} :
      Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ 2 := by
  classical
  obtain ⟨S, hScard, hS⟩ :=
    Work.HP.Q44Main.QuadCount.planesNotRadFinset Q hQ hQ0 hnolf hpe
      (fun hc => hp ((Work.HP.Q44Main.QuadCount.radSub_mem_iff Q hQ
        (Work.Q44Geom.toRatLM p.2)).mpr hc))
  set G : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | L ∈ SC Q s ∧ cpair Q s L = p} with hGdef
  have hinj : Set.InjOn (fun L : Submodule ℤ (Fin 5 → ℤ) => Work.Q44Geom.ratSpan L) G := by
    intro L hL L' hL' h
    exact eq_of_ratSpan_eq hL.1.1.1 hL'.1.1.1 h
  have hmaps : ∀ L ∈ G, Work.Q44Geom.ratSpan L ∈ S := by
    intro L hL
    obtain ⟨hLs, hcp⟩ := hL
    obtain ⟨hQset, -⟩ := hLs
    refine hS _ (Work.Q44Geom.ratSpan_finrank L hQset.2.1) ?_ ?_
    · rw [← hcp]
      exact (Work.Q44Geom.sat_span L hQset.1 (cpair Q s L).2).mp (cpair_spec hQset).2.1
    · intro v hv
      exact eval_zero_of_mem_ratSpan Q hQ (fun x hx => hQset.2.2.2 x hx) hv
  have hstep : G.ncard ≤ S.card := by
    have h1 := Set.ncard_le_ncard_of_injOn
      (fun L : Submodule ℤ (Fin 5 → ℤ) => Work.Q44Geom.ratSpan L) hmaps hinj S.finite_toSet
    rwa [Set.ncard_coe_finset] at h1
  have h2 : G.ncard ≤ 2 := le_trans hstep hScard
  exact_mod_cast h2

/-! ## The three case bounds -/

lemma SA_bound (Cz : ℝ) (hCzpos : 0 < Cz)
    (hCz : ∀ (f : MvPolynomial (Fin 5) ℚ), f ≠ 0 → f.totalDegree ≤ 4 → ∀ T : ℝ, 1 ≤ T →
      (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧
          MvPolynomial.eval (fun i => (x i : ℚ)) f = 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ) ≤ Cz * T ^ 4)
    (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hnolf : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False)
    (s : Fin 3 → ℝ) (hs0 : 1 ≤ s 0) (hs01 : s 0 ≤ s 1) (hs12 : s 1 ≤ s 2) :
    ((SA Q s).ncard : ℝ) ≤ 2 * (Cz * s 0 ^ 4) * (Cz * s 1 ^ 4) := by
  classical
  have hQsetFin : (Qset Q s).Finite :=
    (Sig2.Tset_finite 3 s).subset (fun L hL => ⟨hL.1, hL.2.1, hL.2.2.1⟩)
  have hSfin : (SA Q s).Finite := hQsetFin.subset (fun L hL => hL.1)
  have hfiber : ∀ p : (Fin 5 → ℤ) × (Fin 5 → ℤ),
      ((SA Q s) ∩ (cpair Q s) ⁻¹' {p}).ncard ≤ 2 := by
    intro p
    by_cases hp : p ∈ cpair Q s '' (SA Q s)
    · obtain ⟨L₀, hL₀, hL₀p⟩ := hp
      obtain ⟨hQset₀, hnotmem⟩ := hL₀
      have hp1 : p.1 = (cpair Q s L₀).1 := by rw [← hL₀p]
      have hspec := cpair_spec hQset₀
      have hnotmem' : Work.Q44Geom.toRatLM p.1 ∉ radSub Q := by rw [hp1]; exact hnotmem
      have hpe : MvPolynomial.eval (fun i => (p.1 i : ℚ)) Q = 0 := by
        rw [hp1]
        exact hQset₀.2.2.2 _ hspec.1
      have hsub : (SA Q s) ∩ (cpair Q s) ⁻¹' {p} ⊆
          {L : Submodule ℤ (Fin 5 → ℤ) | L ∈ SA Q s ∧ cpair Q s L = p} := by
        intro L hL
        exact ⟨hL.1, by simpa using hL.2⟩
      have hfin : ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ SA Q s ∧ cpair Q s L = p} :
          Set (Submodule ℤ (Fin 5 → ℤ))).Finite := hSfin.subset (fun L hL => hL.1)
      have h1 : (((SA Q s) ∩ (cpair Q s) ⁻¹' {p}).ncard : ℝ) ≤
          (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ SA Q s ∧ cpair Q s L = p} :
            Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
      have h2 := fiber_SA_le_two Q hQ hQ0 hnolf s p hnotmem' hpe
      have h3 : (((SA Q s) ∩ (cpair Q s) ⁻¹' {p}).ncard : ℝ) ≤ 2 := le_trans h1 h2
      exact_mod_cast h3
    · have hemp : (SA Q s) ∩ (cpair Q s) ⁻¹' {p} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro L ⟨hL, hLp⟩
        exact hp ⟨L, hL, hLp⟩
      rw [hemp]
      simp
  have hmain : (SA Q s).ncard ≤ 2 * (cpair Q s '' (SA Q s)).ncard :=
    Work.Q44Geom.ncard_le_mul_image hSfin (cpair Q s) 2 hfiber
  have hrange : cpair Q s '' (SA Q s) ⊆
      ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 0 ∧
          MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)) ×ˢ
      ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
          MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)) := by
    rintro p ⟨L, hL, hLp⟩
    obtain ⟨hQset, -⟩ := hL
    have hspec := cpair_spec hQset
    exact ⟨⟨by rw [← hLp]; exact hspec.2.2.2.1,
            by rw [← hLp]; exact hQset.2.2.2 _ hspec.1⟩,
           ⟨by rw [← hLp]; exact hspec.2.2.2.2,
            by rw [← hLp]; exact hQset.2.2.2 _ hspec.2.1⟩⟩
  have hfinA : ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 0 ∧
      MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)).Finite :=
    (MDBasic.finite_eNorm_le (s 0)).subset (fun x hx => hx.1)
  have hfinB : ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
      MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)).Finite :=
    (MDBasic.finite_eNorm_le (s 1)).subset (fun x hx => hx.1)
  have hA : (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 0 ∧
      MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ Cz * s 0 ^ 4 := hCz Q hQ0 (le_trans hQ.totalDegree_le (by norm_num : (2 : ℕ) ≤ 4)) (s 0) hs0
  have hB : (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
      MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ Cz * s 1 ^ 4 := hCz Q hQ0 (le_trans hQ.totalDegree_le (by norm_num : (2 : ℕ) ≤ 4)) (s 1) (le_trans hs0 hs01)
  have hstep1 : ((cpair Q s '' (SA Q s)).ncard : ℝ) ≤ (Cz * s 0 ^ 4) * (Cz * s 1 ^ 4) := by
    have h1 : ((cpair Q s '' (SA Q s)).ncard : ℕ) ≤
        (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 0 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)) ×ˢ
          ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ))).ncard :=
      Set.ncard_le_ncard hrange (hfinA.prod hfinB)
    have h2 : ((({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 0 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)) ×ˢ
          ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ))).ncard : ℝ)
        = (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 0 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)).ncard : ℝ)
          * (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)).ncard : ℝ) := by
      rw [Set.ncard_prod, Nat.cast_mul]
    calc ((cpair Q s '' (SA Q s)).ncard : ℝ)
        ≤ ((({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 0 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)) ×ˢ
          ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ))).ncard : ℝ) := by
          exact_mod_cast h1
      _ ≤ (Cz * s 0 ^ 4) * (Cz * s 1 ^ 4) := by
          rw [h2]
          refine mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity)
  calc ((SA Q s).ncard : ℝ) ≤ 2 * ((cpair Q s '' (SA Q s)).ncard : ℝ) := by
        exact_mod_cast hmain
    _ ≤ 2 * ((Cz * s 0 ^ 4) * (Cz * s 1 ^ 4)) :=
        mul_le_mul_of_nonneg_left hstep1 (by norm_num)
    _ = 2 * (Cz * s 0 ^ 4) * (Cz * s 1 ^ 4) := by ring

lemma SC_bound (Cz Kc : ℝ) (hCzpos : 0 < Cz) (hKcpos : 0 < Kc)
    (hCz : ∀ (f : MvPolynomial (Fin 5) ℚ), f ≠ 0 → f.totalDegree ≤ 4 → ∀ T : ℝ, 1 ≤ T →
      (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧
          MvPolynomial.eval (fun i => (x i : ℚ)) f = 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ) ≤ Cz * T ^ 4)
    (hKc : ∀ (L : Submodule ℤ (Fin 5 → ℤ)) (T : ℝ), 0 ≤ T →
      (Work.HP.ballCount L T : ℝ) ≤ Kc * (T + 1) ^ (Work.HP.rk L))
    (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hnolf : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False)
    (s : Fin 3 → ℝ) (hs0 : 1 ≤ s 0) (hs01 : s 0 ≤ s 1) (hs12 : s 1 ≤ s 2)
    (hr : Module.finrank ℚ (radSub Q) ≤ 2) :
    ((SC Q s).ncard : ℝ) ≤ 2 * (Kc * 4 * s 0 ^ 2) * (Cz * s 1 ^ 4) := by
  classical
  have hQsetFin : (Qset Q s).Finite :=
    (Sig2.Tset_finite 3 s).subset (fun L hL => ⟨hL.1, hL.2.1, hL.2.2.1⟩)
  have hSfin : (SC Q s).Finite := hQsetFin.subset (fun L hL => hL.1)
  have hfiber : ∀ p : (Fin 5 → ℤ) × (Fin 5 → ℤ),
      ((SC Q s) ∩ (cpair Q s) ⁻¹' {p}).ncard ≤ 2 := by
    intro p
    by_cases hp : p ∈ cpair Q s '' (SC Q s)
    · obtain ⟨L₀, hL₀, hL₀p⟩ := hp
      obtain ⟨hQset₀, -, hnotmem⟩ := hL₀
      have hp2 : p.2 = (cpair Q s L₀).2 := by rw [← hL₀p]
      have hspec := cpair_spec hQset₀
      have hnotmem' : Work.Q44Geom.toRatLM p.2 ∉ radSub Q := by rw [hp2]; exact hnotmem
      have hpe : MvPolynomial.eval (fun i => (p.2 i : ℚ)) Q = 0 := by
        rw [hp2]
        exact hQset₀.2.2.2 _ hspec.2.1
      have hsub : (SC Q s) ∩ (cpair Q s) ⁻¹' {p} ⊆
          {L : Submodule ℤ (Fin 5 → ℤ) | L ∈ SC Q s ∧ cpair Q s L = p} := by
        intro L hL
        exact ⟨hL.1, by simpa using hL.2⟩
      have hfin : ({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ SC Q s ∧ cpair Q s L = p} :
          Set (Submodule ℤ (Fin 5 → ℤ))).Finite := hSfin.subset (fun L hL => hL.1)
      have h1 : (((SC Q s) ∩ (cpair Q s) ⁻¹' {p}).ncard : ℝ) ≤
          (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ SC Q s ∧ cpair Q s L = p} :
            Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
      have h2 := fiber_SC_le_two Q hQ hQ0 hnolf s p hnotmem' hpe
      have h3 : (((SC Q s) ∩ (cpair Q s) ⁻¹' {p}).ncard : ℝ) ≤ 2 := le_trans h1 h2
      exact_mod_cast h3
    · have hemp : (SC Q s) ∩ (cpair Q s) ⁻¹' {p} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro L ⟨hL, hLp⟩
        exact hp ⟨L, hL, hLp⟩
      rw [hemp]
      simp
  have hmain : (SC Q s).ncard ≤ 2 * (cpair Q s '' (SC Q s)).ncard :=
    Work.Q44Geom.ncard_le_mul_image hSfin (cpair Q s) 2 hfiber
  have hrange : cpair Q s '' (SC Q s) ⊆
      ({x : Fin 5 → ℤ | x ∈ radLatSub Q ∧ Work.HP.eNorm x ≤ s 0} : Set (Fin 5 → ℤ)) ×ˢ
      ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
          MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)) := by
    rintro p ⟨L, hL, hLp⟩
    obtain ⟨hQset, hmem1, -⟩ := hL
    have hspec := cpair_spec hQset
    exact ⟨⟨by rw [← hLp]; exact hmem1, by rw [← hLp]; exact hspec.2.2.2.1⟩,
           ⟨by rw [← hLp]; exact hspec.2.2.2.2,
            by rw [← hLp]; exact hQset.2.2.2 _ hspec.2.1⟩⟩
  have hfinA : ({x : Fin 5 → ℤ | x ∈ radLatSub Q ∧ Work.HP.eNorm x ≤ s 0} :
      Set (Fin 5 → ℤ)).Finite :=
    (MDBasic.finite_eNorm_le (s 0)).subset (fun x hx => hx.2)
  have hfinB : ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
      MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)).Finite :=
    (MDBasic.finite_eNorm_le (s 1)).subset (fun x hx => hx.1)
  have hs0n : (0 : ℝ) ≤ s 0 := le_trans zero_le_one hs0
  have hA : (({x : Fin 5 → ℤ | x ∈ radLatSub Q ∧ Work.HP.eNorm x ≤ s 0} :
      Set (Fin 5 → ℤ)).ncard : ℝ) ≤ Kc * 4 * s 0 ^ 2 := by
    have h1 : (({x : Fin 5 → ℤ | x ∈ radLatSub Q ∧ Work.HP.eNorm x ≤ s 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ) = (Work.HP.ballCount (radLatSub Q) (s 0) : ℝ) := rfl
    rw [h1]
    have h2 := hKc (radLatSub Q) (s 0) hs0n
    have h3 : Work.HP.rk (radLatSub Q) = Module.finrank ℚ (radSub Q) :=
      Work.HP.Q44Main.QuadCount.radLatSub_rank Q
    rw [h3] at h2
    have h4 : (s 0 + 1) ^ Module.finrank ℚ (radSub Q) ≤ (2 * s 0) ^ 2 := by
      have h5 : Module.finrank ℚ (radSub Q) ≤ 2 := hr
      calc (s 0 + 1) ^ Module.finrank ℚ (radSub Q) ≤ (s 0 + 1) ^ 2 :=
            pow_le_pow_right₀ (by linarith) h5
        _ ≤ (2 * s 0) ^ 2 := by
            have : s 0 + 1 ≤ 2 * s 0 := by linarith
            exact pow_le_pow_left₀ (by linarith) this 2
    have h6 : (0 : ℝ) ≤ Kc := by
      have h8 := hKc (⊥ : Submodule ℤ (Fin 5 → ℤ)) 0 (le_refl 0)
      rw [show (0 : ℝ) + 1 = 1 by norm_num, one_pow, mul_one] at h8
      have h9 : (0 : ℝ) ≤ (Work.HP.ballCount (⊥ : Submodule ℤ (Fin 5 → ℤ)) 0 : ℝ) :=
        Nat.cast_nonneg _
      linarith
    calc (Work.HP.ballCount (radLatSub Q) (s 0) : ℝ) ≤ Kc * (s 0 + 1) ^ Module.finrank ℚ (radSub Q) := h2
      _ ≤ Kc * (2 * s 0) ^ 2 := mul_le_mul_of_nonneg_left h4 h6
      _ = Kc * 4 * s 0 ^ 2 := by ring
  have hB : (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
      MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ Cz * s 1 ^ 4 := hCz Q hQ0 (le_trans hQ.totalDegree_le (by norm_num : (2 : ℕ) ≤ 4)) (s 1) (le_trans hs0 hs01)
  have hstep1 : ((cpair Q s '' (SC Q s)).ncard : ℝ) ≤ (Kc * 4 * s 0 ^ 2) * (Cz * s 1 ^ 4) := by
    have h1 : ((cpair Q s '' (SC Q s)).ncard : ℕ) ≤
        (({x : Fin 5 → ℤ | x ∈ radLatSub Q ∧ Work.HP.eNorm x ≤ s 0} : Set (Fin 5 → ℤ)) ×ˢ
          ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ))).ncard :=
      Set.ncard_le_ncard hrange (hfinA.prod hfinB)
    have h2 : ((({x : Fin 5 → ℤ | x ∈ radLatSub Q ∧ Work.HP.eNorm x ≤ s 0} :
            Set (Fin 5 → ℤ)) ×ˢ
          ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ))).ncard : ℝ)
        = (({x : Fin 5 → ℤ | x ∈ radLatSub Q ∧ Work.HP.eNorm x ≤ s 0} :
            Set (Fin 5 → ℤ)).ncard : ℝ)
          * (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
            MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ)).ncard : ℝ) := by
      rw [Set.ncard_prod, Nat.cast_mul]
    calc ((cpair Q s '' (SC Q s)).ncard : ℝ)
        ≤ ((({x : Fin 5 → ℤ | x ∈ radLatSub Q ∧ Work.HP.eNorm x ≤ s 0} :
              Set (Fin 5 → ℤ)) ×ˢ
            ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ s 1 ∧
              MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} : Set (Fin 5 → ℤ))).ncard : ℝ) := by
          exact_mod_cast h1
      _ ≤ (Kc * 4 * s 0 ^ 2) * (Cz * s 1 ^ 4) := by
          rw [h2]
          refine mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity)
  calc ((SC Q s).ncard : ℝ) ≤ 2 * ((cpair Q s '' (SC Q s)).ncard : ℝ) := by
        exact_mod_cast hmain
    _ ≤ 2 * ((Kc * 4 * s 0 ^ 2) * (Cz * s 1 ^ 4)) :=
        mul_le_mul_of_nonneg_left hstep1 (by norm_num)
    _ = 2 * (Kc * 4 * s 0 ^ 2) * (Cz * s 1 ^ 4) := by ring

/-- The first vector of the canonical pair is nonzero. -/
lemma fst_cpair_ne_zero {Q : MvPolynomial (Fin 5) ℚ} {s : Fin 3 → ℝ}
    {L : Submodule ℤ (Fin 5 → ℤ)} (hQset : L ∈ Qset Q s) : (cpair Q s L).1 ≠ 0 := by
  intro h0
  have hli := (cpair_spec hQset).2.2.1
  rw [Fintype.linearIndependent_iff] at hli
  have h1 : (∑ j : Fin 2, (![1, 0] : Fin 2 → ℤ) j • ![(cpair Q s L).1, (cpair Q s L).2] j)
      = 0 := by
    rw [Fin.sum_univ_two]
    simp [h0]
  have h2 := hli ![1, 0] h1 0
  simpa using h2

/-- In the case `SB`, the whole integral radical is contained in `L`. -/
lemma radLatSub_le_of_cpair_mem {Q : MvPolynomial (Fin 5) ℚ}
    {s : Fin 3 → ℝ} {L : Submodule ℤ (Fin 5 → ℤ)} (hQset : L ∈ Qset Q s)
    (hmem1 : Work.Q44Geom.toRatLM (cpair Q s L).1 ∈ radSub Q)
    (hmem2 : Work.Q44Geom.toRatLM (cpair Q s L).2 ∈ radSub Q)
    (hr : Module.finrank ℚ (radSub Q) ≤ 2) : radLatSub Q ≤ L := by
  classical
  have hspec := cpair_spec hQset
  obtain ⟨hprim, -, -, -⟩ := hQset
  have hliQ : LinearIndependent ℚ ![Work.Q44Geom.toRatLM (cpair Q s L).1,
      Work.Q44Geom.toRatLM (cpair Q s L).2] :=
    Work.Q44Geom.rat_coerce_linIndep _ _ hspec.2.2.1
  have hspan_le : Submodule.span ℚ ({Work.Q44Geom.toRatLM (cpair Q s L).1,
      Work.Q44Geom.toRatLM (cpair Q s L).2} : Set (Fin 5 → ℚ)) ≤ radSub Q := by
    rw [Submodule.span_le]
    rintro v (hv | hv)
    · rw [hv]; exact hmem1
    · rw [hv]; exact hmem2
  have hfin_span : Module.finrank ℚ (Submodule.span ℚ ({Work.Q44Geom.toRatLM (cpair Q s L).1,
      Work.Q44Geom.toRatLM (cpair Q s L).2} : Set (Fin 5 → ℚ))) = 2 :=
    finrank_span_pair hliQ
  have hfin2 : Module.finrank ℚ (radSub Q) = 2 := by
    have h2le : 2 ≤ Module.finrank ℚ (radSub Q) := by
      rw [← hfin_span]
      exact Submodule.finrank_mono hspan_le
    omega
  have hspan_eq : Submodule.span ℚ ({Work.Q44Geom.toRatLM (cpair Q s L).1,
      Work.Q44Geom.toRatLM (cpair Q s L).2} : Set (Fin 5 → ℚ)) = radSub Q :=
    Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hfin_span, hfin2])
  intro x hx
  have hxmem : Work.Q44Geom.toRatLM x ∈ radSub Q := hx
  rw [← hspan_eq] at hxmem
  have hrat : Work.Q44Geom.toRatLM x ∈ Work.Q44Geom.ratSpan
      (Submodule.span ℤ ({(cpair Q s L).1, (cpair Q s L).2} : Set (Fin 5 → ℤ))) := by
    rw [ratSpan_span_pair]
    exact hxmem
  obtain ⟨n, hn, hmem⟩ := (Work.Q44Geom.mem_ratSpan_iff _ x).mp hrat
  refine hprim x n hn ?_
  refine (Submodule.span_le.mpr ?_) hmem
  rintro y (hy | hy)
  · rw [hy]; exact hspec.1
  · rw [hy]; exact hspec.2.1

/-- In the case `SB` (only possible in radical dimension `2`), the lattices are superlattices of
the fixed lattice `radLatSub Q` with `detL L ≤ s 0 * s 1 * s 2`. -/
lemma SB_bound (Cw : ℝ) (hCwpos : 0 < Cw)
    (hCw : ∀ (Λ : Submodule ℤ (Fin 5 → ℤ)) (s : Fin 3 → ℝ),
      Work.HP.rk Λ = 2 → Work.HP.IsPrimLat Λ →
      1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 → Work.HP.detL Λ ≤ s 0 * s 1 →
      (({L : Submodule ℤ (Fin 5 → ℤ) | Λ ≤ L ∧ Work.HP.rk L = 3 ∧ Work.HP.IsPrimLat L ∧
        (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j)} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard
          : ℝ) ≤ Cw * (s 0 * s 1 * s 2) ^ 3)
    (Q : MvPolynomial (Fin 5) ℚ)
    (s : Fin 3 → ℝ) (hs0 : 1 ≤ s 0) (hs01 : s 0 ≤ s 1) (hs12 : s 1 ≤ s 2)
    (hr : Module.finrank ℚ (radSub Q) ≤ 2) :
    ((SB Q s).ncard : ℝ) ≤ Cw * (s 0 * s 1 * s 2) ^ 3 := by
  classical
  by_cases hne : (SB Q s).Nonempty
  · obtain ⟨L₀, hL₀⟩ := hne
    obtain ⟨hQset₀, hmem1₀, hmem2₀⟩ := hL₀
    have hspec₀ := cpair_spec hQset₀
    have hb1ne : (cpair Q s L₀).1 ≠ 0 := fst_cpair_ne_zero hQset₀
    have hliQ : LinearIndependent ℚ ![Work.Q44Geom.toRatLM (cpair Q s L₀).1,
        Work.Q44Geom.toRatLM (cpair Q s L₀).2] :=
      Work.Q44Geom.rat_coerce_linIndep _ _ hspec₀.2.2.1
    have hspan_le : Submodule.span ℚ ({Work.Q44Geom.toRatLM (cpair Q s L₀).1,
        Work.Q44Geom.toRatLM (cpair Q s L₀).2} : Set (Fin 5 → ℚ)) ≤ radSub Q := by
      rw [Submodule.span_le]
      rintro v (hv | hv)
      · rw [hv]; exact hmem1₀
      · rw [hv]; exact hmem2₀
    have hfin_span : Module.finrank ℚ (Submodule.span ℚ ({Work.Q44Geom.toRatLM (cpair Q s L₀).1,
        Work.Q44Geom.toRatLM (cpair Q s L₀).2} : Set (Fin 5 → ℚ))) = 2 :=
      finrank_span_pair hliQ
    have hfin2 : Module.finrank ℚ (radSub Q) = 2 := by
      have h2le : 2 ≤ Module.finrank ℚ (radSub Q) := by
        rw [← hfin_span]
        exact Submodule.finrank_mono hspan_le
      omega
    have hrk : Work.HP.rk (radLatSub Q) = 2 := by
      rw [Work.HP.Q44Main.QuadCount.radLatSub_rank Q, hfin2]
    have hlam1 : Work.HP.lam (radLatSub Q) 1 ≤ s 0 :=
      le_trans (Work.HP.lam_one_le_eNorm _ hmem1₀ hb1ne) hspec₀.2.2.2.1
    have hlam2 : Work.HP.lam (radLatSub Q) 2 ≤ s 1 := by
      refine le_trans (Work.HP.lam_two_le_max _ hmem1₀ hmem2₀ hspec₀.2.2.1) ?_
      rw [max_le_iff]
      exact ⟨le_trans hspec₀.2.2.2.1 hs01, hspec₀.2.2.2.2⟩
    have hdet : Work.HP.detL (radLatSub Q) ≤ s 0 * s 1 := by
      have h1 : Work.HP.detL (radLatSub Q)
          ≤ Work.HP.lam (radLatSub Q) 1 * Work.HP.lam (radLatSub Q) 2 := by
        have h2 := detL_le_prod_lam (radLatSub Q)
        rw [hrk] at h2
        rw [Finset.prod_range_succ, Finset.prod_range_one] at h2
        simpa using h2
      refine le_trans h1 (mul_le_mul hlam1 hlam2 ?_ ?_)
      · exact Work.HP.lam_nonneg (radLatSub Q) 2
      · linarith
    have hsub : SB Q s ⊆
        {L : Submodule ℤ (Fin 5 → ℤ) | radLatSub Q ≤ L ∧ Work.HP.rk L = 3 ∧
          Work.HP.IsPrimLat L ∧ (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j)} := by
      intro L hL
      obtain ⟨hQset, hmem1, hmem2⟩ := hL
      exact ⟨radLatSub_le_of_cpair_mem hQset hmem1 hmem2 hr, hQset.2.1, hQset.1, hQset.2.2.1⟩
    have hfin : ({L : Submodule ℤ (Fin 5 → ℤ) | radLatSub Q ≤ L ∧ Work.HP.rk L = 3 ∧
        Work.HP.IsPrimLat L ∧ (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j)} :
        Set (Submodule ℤ (Fin 5 → ℤ))).Finite :=
      (Sig2.Tset_finite 3 s).subset (fun L hL => ⟨hL.2.2.1, hL.2.1, hL.2.2.2⟩)
    have h1 : ((SB Q s).ncard : ℝ)
        ≤ (({L : Submodule ℤ (Fin 5 → ℤ) | radLatSub Q ≤ L ∧ Work.HP.rk L = 3 ∧
            Work.HP.IsPrimLat L ∧ (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j)} :
            Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hfin
    exact le_trans h1 (hCw (radLatSub Q) s hrk (isPrimLat_radLatSub Q) hs0 hs01 hs12 hdet)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty, Nat.cast_zero]
    have h1 : (0 : ℝ) < s 0 * s 1 * s 2 := lt_of_lt_of_le zero_lt_one
      (one_le_prod s hs0 hs01 hs12)
    exact le_of_lt (mul_pos hCwpos (pow_pos h1 3))

/-! ## The case of a large radical -/

/-- If `3 ≤ finrank (radSub Q)`, every lattice of the counting set equals `radLatSub Q`. -/
lemma Qset_subset_singleton (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hnolf : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False)
    (s : Fin 3 → ℝ) (h3le : 3 ≤ Module.finrank ℚ (radSub Q)) :
    Qset Q s ⊆ ({radLatSub Q} : Set (Submodule ℤ (Fin 5 → ℤ))) := by
  classical
  have hle3 := Work.HP.Q44Main.QuadCount.finrank_radSub_le_three Q hQ hQ0 hnolf
  have hfin3 : Module.finrank ℚ (radSub Q) = 3 := le_antisymm hle3 h3le
  intro L hL
  have hLrad : L ≤ radLatSub Q := by
    intro x hx
    have h1 : MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0 := hL.2.2.2 x hx
    have h2 : Work.Q44Geom.toRatLM x ∈ coneQ Q := h1
    have h3 : Work.Q44Geom.toRatLM x ∈ radQ Q :=
      coneInRad Q hQ hnolf (radSub Q)
        (fun u => (Work.HP.Q44Main.QuadCount.radSub_mem_iff Q hQ u)) h3le h2
    exact (Work.HP.Q44Main.QuadCount.radSub_mem_iff Q hQ _).mpr h3
  have hle : Work.Q44Geom.ratSpan L ≤ radSub Q := by
    intro v hv
    obtain ⟨n, hn, hmem⟩ := (Work.Q44Geom.mem_ratSpan_iff' L v).mp hv
    obtain ⟨w, hwL, hw⟩ := Submodule.mem_map.mp hmem
    have h4 : Work.Q44Geom.toRatLM w ∈ radSub Q := hLrad hwL
    have h5 : ((n : ℚ)) ≠ 0 := by exact_mod_cast hn
    have h6 : n • v = (n : ℚ) • v := Int.cast_smul_eq_zsmul ℚ n v
    have h7 : n • v ∈ radSub Q := by rw [← hw]; exact h4
    have h8 : ((n : ℚ)) • v ∈ radSub Q := by rwa [h6] at h7
    have h9 : ((n : ℚ))⁻¹ • (((n : ℚ)) • v) ∈ radSub Q := Submodule.smul_mem _ _ h8
    rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at h9
  have h1 : Module.finrank ℚ (Work.Q44Geom.ratSpan L) = 3 :=
    Work.Q44Geom.ratSpan_finrank L hL.2.1
  have hspan : Work.Q44Geom.ratSpan L = radSub Q :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, hfin3])
  have : L = radLatSub Q := by
    ext x
    rw [show x ∈ radLatSub Q ↔ Work.Q44Geom.toRatLM x ∈ radSub Q from Iff.rfl, ← hspan,
      Work.Q44Geom.sat_span L hL.1 x]
  simpa [this]

/-! ## The main theorem -/

theorem latS_quad_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : MvPolynomial (Fin 5) ℚ), Q.IsHomogeneous 2 → Q ≠ 0 →
      (∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False) →
      ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
        (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
           (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
           (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0)} :
          Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
          ≤ C * (s 0 * s 1 * s 2) ^ 3 := by
  classical
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.Q44Geom.zero_count
  obtain ⟨Kc, hKcpos, hKc⟩ := Work.HP.ballCount_le_pow_rk (ι := Fin 5)
  obtain ⟨Cw, hCwpos, hCw⟩ := Work.HP.Q44Main.QuadCount.superlattice_window_count
  refine ⟨2 * Cz ^ 2 + Cw + 2 * (Kc * 4) * Cz + 1, by positivity, ?_⟩
  intro Q hQ hQ0 hnolf s hs0 hs01 hs12
  have hprod1 : (1 : ℝ) ≤ s 0 * s 1 * s 2 := one_le_prod s hs0 hs01 hs12
  have hprodpos : (0 : ℝ) < s 0 * s 1 * s 2 := lt_of_lt_of_le zero_lt_one hprod1
  by_cases hr : Module.finrank ℚ (radSub Q) ≤ 2
  · have hQsetFin : (Qset Q s).Finite :=
      (Sig2.Tset_finite 3 s).subset (fun L hL => ⟨hL.1, hL.2.1, hL.2.2.1⟩)
    have hSAfin : (SA Q s).Finite := hQsetFin.subset (fun L hL => hL.1)
    have hSBfin : (SB Q s).Finite := hQsetFin.subset (fun L hL => hL.1)
    have hSCfin : (SC Q s).Finite := hQsetFin.subset (fun L hL => hL.1)
    have hunionfin : (SA Q s ∪ (SB Q s ∪ SC Q s)).Finite := hSAfin.union (hSBfin.union hSCfin)
    have h1 : ((Qset Q s).ncard : ℝ) ≤ ((SA Q s ∪ (SB Q s ∪ SC Q s)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard (Qset_subset_cases Q s) hunionfin
    have h2 : (((SA Q s ∪ (SB Q s ∪ SC Q s)).ncard : ℕ) : ℝ)
        ≤ (SA Q s).ncard + ((SB Q s ∪ SC Q s).ncard : ℝ) := by
      have := Set.ncard_union_le (SA Q s) (SB Q s ∪ SC Q s)
      exact_mod_cast this
    have h3 : (((SB Q s ∪ SC Q s).ncard : ℕ) : ℝ) ≤ (SB Q s).ncard + (SC Q s).ncard := by
      have := Set.ncard_union_le (SB Q s) (SC Q s)
      exact_mod_cast this
    have hA := SA_bound Cz hCzpos hCz Q hQ hQ0 hnolf s hs0 hs01 hs12
    have hB := SB_bound Cw hCwpos hCw Q s hs0 hs01 hs12 hr
    have hC := SC_bound Cz Kc hCzpos hKcpos hCz hKc Q hQ hQ0 hnolf s hs0 hs01 hs12 hr
    have harith : s 0 ^ 4 * s 1 ^ 4 ≤ (s 0 * s 1 * s 2) ^ 3 := sq_four_le s hs0 hs01 hs12
    have harith2 : s 0 ^ 2 * s 1 ^ 4 ≤ (s 0 * s 1 * s 2) ^ 3 :=
      sq_two_four_le s hs0 hs01 hs12
    have hP : (0 : ℝ) < (s 0 * s 1 * s 2) ^ 3 := pow_pos hprodpos 3
    have hAn : (SA Q s).ncard ≤ 2 * Cz ^ 2 * (s 0 * s 1 * s 2) ^ 3 := by
      refine le_trans hA ?_
      calc 2 * (Cz * s 0 ^ 4) * (Cz * s 1 ^ 4) = 2 * Cz ^ 2 * (s 0 ^ 4 * s 1 ^ 4) := by ring
        _ ≤ 2 * Cz ^ 2 * (s 0 * s 1 * s 2) ^ 3 := by
            refine mul_le_mul_of_nonneg_left harith ?_
            positivity
    have hBn : (SB Q s).ncard ≤ Cw * (s 0 * s 1 * s 2) ^ 3 := hB
    have hCn : (SC Q s).ncard ≤ 2 * (Kc * 4) * Cz * (s 0 * s 1 * s 2) ^ 3 := by
      refine le_trans hC ?_
      calc 2 * (Kc * 4 * s 0 ^ 2) * (Cz * s 1 ^ 4) = 2 * (Kc * 4) * Cz * (s 0 ^ 2 * s 1 ^ 4) := by
            ring
        _ ≤ 2 * (Kc * 4) * Cz * (s 0 * s 1 * s 2) ^ 3 := by
            refine mul_le_mul_of_nonneg_left harith2 ?_
            positivity
    have hfinal : ((Qset Q s).ncard : ℝ)
        ≤ (2 * Cz ^ 2 + Cw + 2 * (Kc * 4) * Cz + 1) * (s 0 * s 1 * s 2) ^ 3 := by
      have hsum : ((Qset Q s).ncard : ℝ)
          ≤ (SA Q s).ncard + (SB Q s).ncard + (SC Q s).ncard := by linarith
      calc ((Qset Q s).ncard : ℝ)
          ≤ (SA Q s).ncard + (SB Q s).ncard + (SC Q s).ncard := hsum
        _ ≤ 2 * Cz ^ 2 * (s 0 * s 1 * s 2) ^ 3 + Cw * (s 0 * s 1 * s 2) ^ 3
              + 2 * (Kc * 4) * Cz * (s 0 * s 1 * s 2) ^ 3 := by linarith
        _ ≤ (2 * Cz ^ 2 + Cw + 2 * (Kc * 4) * Cz + 1) * (s 0 * s 1 * s 2) ^ 3 := by
            nlinarith [hP]
    exact hfinal
  · have h3le : 3 ≤ Module.finrank ℚ (radSub Q) := by
      have := not_le.mp hr
      omega
    have hsub := Qset_subset_singleton Q hQ hQ0 hnolf s h3le
    have hcard : ((Qset Q s).ncard : ℝ) ≤ 1 := by
      have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton (radLatSub Q))
      rw [Set.ncard_singleton] at h1
      exact_mod_cast h1
    have h1 : (1 : ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hprod1 3
      simpa using this
    have hbound : (1 : ℝ) ≤ (2 * Cz ^ 2 + Cw + 2 * (Kc * 4) * Cz + 1) * (s 0 * s 1 * s 2) ^ 3 := by
      have hpos : (1 : ℝ) ≤ 2 * Cz ^ 2 + Cw + 2 * (Kc * 4) * Cz + 1 := by
        nlinarith [hCzpos, hKcpos, hCwpos, sq_nonneg Cz]
      nlinarith [h1, hpos]
    calc ((Qset Q s).ncard : ℝ) ≤ 1 := hcard
      _ ≤ (2 * Cz ^ 2 + Cw + 2 * (Kc * 4) * Cz + 1) * (s 0 * s 1 * s 2) ^ 3 := hbound

end Work.HP.Q44Main

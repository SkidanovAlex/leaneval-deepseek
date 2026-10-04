import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.BPair_Rstar
import Submission.Work.Diff.STE.B3.BPair_J_lin
import Submission.Work.Diff.STE.B3.STruncR_selfadjoint
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.B3.JPrelim
import Submission.Work.Diff.STE.B3.Pair
import Submission.Work.Diff.STE.B3.integrableOn_Cpair_term
import Submission.Work.Diff.STE.B3.integrableOn_Rpair_term

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the Friedrichs mollifier `J ρ ε` is self-adjoint for the composite pairing

This file proves `Work.Diff.STE.B3.BPair_J_self`:
`D.BPair (D.J ρ ε h) k = D.BPair h (D.J ρ ε k)`.

The mollifier is `J ρ ε h = Σ_i R_i*(S_ε (R_i h))` with `S_ε = STruncR ρ ε` the real Fourier
multiplier of multiplier `ρ (ε • ·)`.  The proof is the composition of three pieces:

* `Work.Diff.STE.B3.BPair_J_lin` (delegated): `BPair (Σ_i R_i* u_i) k = Σ_i CPair_i (u_i) (R_i k)`;
* `Work.Diff.STE.B3.STruncR_selfadjoint` (delegated), fed with
  `Work.Diff.STE.B3.fourierCoeff_periodization` (delegated): on the centred cube the unweighted `L²`
  pairing is symmetric under the *real* Fourier multiplier `STruncR ρ ε`;
* the elementary integrability facts for the localised components `R i h a b` and their support in
  the open unit cube.

The local lemmas `perCoeff_eq_integral_aux`, `STruncR_selfadjoint_aux` and `BPair_J_lin_aux` below
are exactly the three delegated statements; they are proved by an immediate call to the delegated
module (see the bottom of this file).
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The localised component `R i h a b` is supported in the open unit cube.  (Boundary-free
version of `Work.Diff.STE.B3Data.R_support`.) -/
lemma support_R_subset (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    Function.support (D.R i h a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)) :=
  fun z hz => D.psi_supp i (fun h0 => hz (by
    simp only [Work.Diff.STE.B3Data.R, h0, zero_mul, mul_zero]))

/-- The localised component `R i h a b` is integrable on the centred cube. -/
lemma integrableOn_R_centreCube (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j h a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0})
    (a b : Fin (Module.finrank ℝ E)) :
    MeasureTheory.IntegrableOn (D.R i h a b)
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume := by
  have h1 := integrableOn_Cpair_term (I := I) (M := M) D i (fun _ _ _ => (1 : ℝ)) h
    (fun a b => continuous_const) hh (dens_bound_sigma D) a b
  simpa only [one_mul] using h1

end Helpers

section Delegated

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The periodisation identity of `Work.Diff.STE.B3.fourierCoeff_periodization`, in the form used
below: for a real function supported in the open cube, the Fourier coefficients of its
periodisation are the integrals of the function against the characters over the centred cube. -/
lemma perCoeff_eq_integral_aux (F : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hF : Function.support F ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (hFi : MeasureTheory.IntegrableOn F
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume)
    (m : Fin (Module.finrank ℝ E) → ℤ) :
    Work.Diff.STE.B3.perCoeff F m
      = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          Work.Diff.STE.fourierExp (-m) z * ((F z : ℝ) : ℂ) := by
  have hsupp : Function.support (fun z => ((F z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)) := by
    intro z hz
    refine hF ?_
    rw [Function.mem_support] at hz ⊢
    intro h0
    exact hz (by rw [h0, Complex.ofReal_zero])
  have hsub : Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))
      ⊆ Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1/2:ℝ)) (1/2)) :=
    Set.pi_mono fun _ _ => fun x hx => ⟨hx.1, le_of_lt hx.2⟩
  have hmem : ∀ z ∉ Work.Diff.STE.B3Data.centreCube (E := E), F z = 0 := by
    intro z hz
    by_contra h
    exact hz (hsub (hF h))
  have hint : MeasureTheory.Integrable (fun z => ((F z : ℝ) : ℂ)) MeasureTheory.volume :=
    (hFi.integrable_of_forall_notMem_eq_zero hmem).ofReal
  exact fourierCoeff_periodization (fun z => ((F z : ℝ) : ℂ)) m hsupp hint

/-- The self-adjointness of the Friedrichs truncation
(`Work.Diff.STE.B3.STruncR_selfadjoint`). -/
lemma STruncR_selfadjoint_aux
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < (∑ i, (y i) ^ 2) → ρ y = 0)
    (f g : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hf_supp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (hg_supp : Function.support g ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (hf_int : MeasureTheory.IntegrableOn f
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume)
    (hg_int : MeasureTheory.IntegrableOn g
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume) :
    (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
        Work.Diff.STE.B3Data.STruncR ρ ε f z * g z)
      = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          f z * Work.Diff.STE.B3Data.STruncR ρ ε g z :=
  STruncR_selfadjoint ρ ε hε hρ0 f g hf_supp hg_supp hf_int hg_int
    (perCoeff_eq_integral_aux f hf_supp hf_int)
    (perCoeff_eq_integral_aux g hg_supp hg_int)

end Delegated

section Lin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The additivity of `BPair` in a sum of reconstructions (`Work.Diff.STE.B3.BPair_J_lin`). -/
lemma BPair_J_lin_aux (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (u : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (u i a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j k a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0}) :
    D.BPair (∑ i, D.Rstar i (u i)) k
      = ∑ i, Work.Diff.STE.B3Data.CPair i (u i) (D.R i k) :=
  BPair_J_lin D k u hu hk

end Lin

theorem BPair_J_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < (∑ i, (y i) ^ 2) → ρ y = 0)
    (ε : ℝ) (hε : 0 < ε)
    (h k : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j h a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0})
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j k a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0}) :
    D.BPair (D.J ρ ε h) k = D.BPair h (D.J ρ ε k) := by
  classical
  -- The two component families of the mollifier.
  let u : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    fun i a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z
  let u' : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    fun i a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i k a b) z
  have hJh : D.J ρ ε h = ∑ i, D.Rstar i (u i) := rfl
  have hJk : D.J ρ ε k = ∑ i, D.Rstar i (u' i) := rfl
  have hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (u i a b) :=
    fun i a b => continuous_STruncR ρ ε hε hρ0 (D.R i h a b)
  have hu' : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (u' i a b) :=
    fun i a b => continuous_STruncR ρ ε hε hρ0 (D.R i k a b)
  have hA : D.BPair (∑ i, D.Rstar i (u i)) k
      = ∑ i, Work.Diff.STE.B3Data.CPair i (u i) (D.R i k) :=
    BPair_J_lin_aux D k u hu hk
  have hB : D.BPair h (∑ i, D.Rstar i (u' i))
      = ∑ i, Work.Diff.STE.B3Data.CPair i (u' i) (D.R i h) := by
    rw [Work.Diff.STE.B3Data.BPair_comm]
    exact BPair_J_lin_aux D h u' hu' hh
  rw [hJh, hJk, hA, hB]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Work.Diff.STE.B3Data.CPair]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h1 : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E), u i a b z * D.R i k a b z)
      = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E), D.R i h a b z * u' i a b z := by
    have hself := STruncR_selfadjoint_aux ρ ε hε hρ0 (D.R i h a b) (D.R i k a b)
      (support_R_subset D i h a b) (support_R_subset D i k a b)
      (integrableOn_R_centreCube D i h hh a b) (integrableOn_R_centreCube D i k hk a b)
    dsimp only [u, u'] at hself ⊢
    exact hself
  rw [h1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)

end Work.Diff.STE.B3

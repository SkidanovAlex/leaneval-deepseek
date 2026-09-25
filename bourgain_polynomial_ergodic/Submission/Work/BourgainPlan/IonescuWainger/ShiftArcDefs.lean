import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Sum
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_sum
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs

/-!
# Shifted major arcs: the frequency support of `f_{α + Σ_A}`

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4 —
Lemma `ortho`(iii) for a sunflower with **core** `A₀` (the form consumed by the proof of Theorem
`ortho-apply`(i)).

Tao's `ortho`(iii) concerns the *shifted* major-arc functions

`f_{Σ_{A₀} + α} := Σ_{γ ∈ Σ_{A₀}} f_{α + γ}`,

whose frequency support is the **union** of the arcs `γ + α + [-ε,ε]` over `γ ∈ Σ_{A₀}` (a
`Q_{A₀}`-torsion translate of the arc around `α`), rather than a single arc `arcSet α ε`.

This file supplies that vocabulary:

* `shiftArcSet X α ε` — the shifted arc `X + α + [-ε,ε]`, and `mem_shiftArcSet`, its membership
  form; `shiftArcSet_eq_iUnion` identifies it with `⋃_{γ ∈ X} arcSet (γ + α) ε`;
* `mem_setSumFin_shiftArcSet` — the Minkowski sum of shifted arcs, explicitly;
* `setSumFin_mono`, `shiftArcSet_mono` — monotonicity in the arc sets;
* `sigmaAFinset_subset_sigmaSubA`, `sigmaSubA_mono` — the `Finset`/`Set` and set-monotonicity facts
  for the arc sets;
* `ftLp_congr`, `hasFreqSupport_mono`, `hasFreqSupport_congr`, `hasFreqSupport_congr_memℓp`,
  `hasFreqSupport_finsetSum` — the elementary band-limitation bookkeeping, and
* `hasFreqSupport_majorArc_shift` — the frequency support of `f_{Σ_{A₀} + α}` is contained in
  `shiftArcSet (Σ_{⊆A₀}) α ε`.

Together with the arithmetic disjointness of shifted arcs (the companion file) this yields Tao's
`ortho`(iii) for a sunflower with core, i.e. the Pythagoras step of the proof of `ortho-apply`(i).
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## The shifted arcs -/

/-- **The shifted arc** `X + α + [-ε,ε]`: the frequency support of the shifted major-arc function
`f_{X + α} = Σ_{γ ∈ X} f_{γ + α}`.  It is the union of the arcs `arcSet (γ + α) ε` over `γ ∈ X`
(see `shiftArcSet_eq_iUnion`). -/
def shiftArcSet (X : Set Circle) (α : Circle) (ε : ℝ) : Set Circle :=
  {ξ | ∃ γ : Circle, γ ∈ X ∧ ∃ θ : ℝ, |θ| ≤ ε ∧ ξ = γ + α + (θ : Circle)}

/-- Membership in a shifted arc, unfolded. -/
theorem mem_shiftArcSet {X : Set Circle} {α ξ : Circle} {ε : ℝ} :
    ξ ∈ shiftArcSet X α ε ↔
      ∃ γ : Circle, γ ∈ X ∧ ∃ θ : ℝ, |θ| ≤ ε ∧ ξ = γ + α + (θ : Circle) :=
  Iff.rfl

/-- The shifted arc is the union of the arcs `arcSet (γ + α) ε` over `γ ∈ X`. -/
theorem shiftArcSet_eq_iUnion (X : Set Circle) (α : Circle) (ε : ℝ) :
    shiftArcSet X α ε = ⋃ γ ∈ X, arcSet (γ + α) ε := by
  ext ξ
  rw [mem_shiftArcSet, Set.mem_iUnion]
  constructor
  · rintro ⟨γ, hγ, θ, hθ, hξ⟩
    exact ⟨γ, Set.mem_iUnion.mpr ⟨hγ, by rw [arcSet]; exact ⟨θ, hθ, hξ⟩⟩⟩
  · rintro ⟨γ, hmem⟩
    rw [Set.mem_iUnion] at hmem
    obtain ⟨hγ, hmem⟩ := hmem
    rw [arcSet] at hmem
    obtain ⟨θ, hθ, hξ⟩ := hmem
    exact ⟨γ, hγ, θ, hθ, hξ⟩

/-- The Minkowski sum of shifted arcs is the set of the sums `Σ_i (γ_i + α_i + θ_i)`
with `γ_i ∈ X`, `|θ_i| ≤ ε`. -/
theorem mem_setSumFin_shiftArcSet {n : ℕ} {X : Set Circle} {α : Fin n → Circle} {ε : ℝ}
    {ξ : Circle} :
    ξ ∈ setSumFin n (fun i => shiftArcSet X (α i) ε) ↔
      ∃ γ : Fin n → Circle, (∀ i, γ i ∈ X) ∧
        ∃ θ : Fin n → ℝ, (∀ i, |θ i| ≤ ε) ∧
          ∑ i, (γ i + α i + (θ i : Circle)) = ξ := by
  constructor
  · rintro ⟨f, hf, hsum⟩
    choose γ hγ θ hθ hf' using fun i => mem_shiftArcSet.mp (hf i)
    exact ⟨γ, hγ, θ, hθ, by rw [← hsum]; exact Finset.sum_congr rfl fun i _ => (hf' i).symm⟩
  · rintro ⟨γ, hγ, θ, hθ, hsum⟩
    exact ⟨fun i => γ i + α i + (θ i : Circle),
      fun i => mem_shiftArcSet.mpr ⟨γ i, hγ i, θ i, hθ i, rfl⟩, hsum⟩

/-- Monotonicity of the Minkowski sum in the summands. -/
theorem setSumFin_mono {G : Type*} [AddCommMonoid G] {n : ℕ} {E E' : Fin n → Set G}
    (h : ∀ i, E i ⊆ E' i) : setSumFin n E ⊆ setSumFin n E' := by
  rintro x ⟨f, hf, rfl⟩
  exact ⟨f, fun i => h i (hf i), rfl⟩

/-- Monotonicity of the shifted arc in the arc set `X`. -/
theorem shiftArcSet_mono {X Y : Set Circle} (hXY : X ⊆ Y) (α : Circle) (ε : ℝ) :
    shiftArcSet X α ε ⊆ shiftArcSet Y α ε := by
  rintro ξ ⟨γ, hγ, θ, hθ, hξ⟩
  exact ⟨γ, hXY hγ, θ, hθ, hξ⟩

/-! ## The arc sets `Σ_A` and `Σ_{⊆ A}` as `Finset`/`Set` -/

/-- Every point of the `Finset` `sigmaAFinset A` of exact-denominator points lies in the `Set`
`sigmaSubA A`: `↑(sigmaAFinset A) ⊆ Σ_{⊆ A} = 𝕋[Q_A]`. -/
theorem sigmaAFinset_subset_sigmaSubA (A : Finset ℕ) :
    ((sigmaAFinset A : Finset Circle) : Set Circle) ⊆ sigmaSubA A := by
  intro x hx
  rw [Finset.mem_coe, sigmaAFinset, Finset.mem_image] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact ⟨(a : ℤ), rfl⟩

/-- Monotonicity of `Σ_{⊆ ·}`: `A ⊆ B` implies `Σ_{⊆ A} ⊆ Σ_{⊆ B}` (the common-denominator
identity `a/Q_A = (a·(Q_B/Q_A))/Q_B`). -/
theorem sigmaSubA_mono {A B : Finset ℕ} (hAB : A ⊆ B) (hB : ∀ q ∈ B, q ≠ 0) :
    sigmaSubA A ⊆ sigmaSubA B := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  have h1 : 1 ≤ QA A :=
    Finset.one_le_prod₀ fun q hq => Nat.one_le_iff_ne_zero.mpr (hB q (hAB hq))
  have h2 : 1 ≤ QA B :=
    Finset.one_le_prod₀ fun q hq => Nat.one_le_iff_ne_zero.mpr (hB q hq)
  exact ⟨a * (((QA B) / (QA A) : ℕ) : ℤ),
    (arcPt_commonDenom h1 h2 (Finset.prod_dvd_prod_of_subset A B (fun q => q) hAB) a).symm⟩

/-! ## Band-limitation bookkeeping -/

/-- The Fourier transform of equal sequences is equal (the two square-summability proofs are
irrelevant). -/
theorem ftLp_congr {h h' : ℤ → ℂ} (hfun : h = h') (hh : Memℓp h 2) (hh' : Memℓp h' 2) :
    ftLp h hh = ftLp h' hh' := by
  subst hfun
  rw [Subsingleton.elim hh hh']

/-- The band-limitation hypothesis is invariant under replacing the sequence by an equal one. -/
theorem hasFreqSupport_congr {h h' : ℤ → ℂ} (hfun : h = h') {hh : Memℓp h 2}
    {hh' : Memℓp h' 2} {E : Set Circle} (H : HasFreqSupport h hh E) :
    HasFreqSupport h' hh' E := by
  have hE := ftLp_congr hfun hh hh'
  simp only [HasFreqSupport] at H ⊢
  filter_upwards [H] with θ hθ hθE
  rw [← hE]
  exact hθ hθE

/-- The band-limitation hypothesis is monotone in the frequency support. -/
theorem hasFreqSupport_mono {h : ℤ → ℂ} {hh : Memℓp h 2} {E E' : Set Circle} (hEE : E ⊆ E')
    (hE : HasFreqSupport h hh E) : HasFreqSupport h hh E' :=
  hE.mono fun _ hθ hθ' => hθ fun hmem => hθ' (hEE hmem)

/-- The band-limitation statement does not depend on the proof of square-summability. -/
theorem hasFreqSupport_congr_memℓp {h : ℤ → ℂ} {hh hh' : Memℓp h 2} {E : Set Circle}
    (hE : HasFreqSupport h hh E) : HasFreqSupport h hh' E := by
  rw [Subsingleton.elim hh hh'] at hE
  exact hE

/-- **The frequency support of a finite sum is contained in the union of the frequency supports**
(`Finset`-indexed form of `hasFreqSupport_sum`). -/
theorem hasFreqSupport_finsetSum {ι : Type*} (T : Finset ι) {f : ι → ℤ → ℂ}
    (hf : ∀ i, Memℓp (f i) 2) {E : ι → Set Circle}
    (hE : ∀ i, HasFreqSupport (f i) (hf i) (E i)) :
    HasFreqSupport (fun m => ∑ i ∈ T, f i m) (Memℓp.finsetSum T (fun i _ => hf i))
      (⋃ i ∈ T, E i) := by
  have hsub := hasFreqSupport_sum (ι := ↥T) (f := fun i => f i.1) (hf := fun i => hf i.1)
    (E := fun i => E i.1) (hE := fun i => hE i.1)
  have hfun : (fun m => ∑ i : ↥T, f i.1 m) = fun m => ∑ i ∈ T, f i m := by
    funext m
    rw [← Finset.sum_attach T (fun i => f i m), Finset.attach_eq_univ]
  have hunion : (⋃ i : ↥T, E i.1) ⊆ ⋃ i ∈ T, E i := by
    rintro ξ hmem
    rw [Set.mem_iUnion] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact Set.mem_iUnion.mpr ⟨i.1, Set.mem_iUnion.mpr ⟨i.2, hi⟩⟩
  have hmid : HasFreqSupport (fun m => ∑ i ∈ T, f i m)
      (Memℓp.finsetSum T (fun i _ => hf i)) (⋃ i : ↥T, E i.1) :=
    hasFreqSupport_congr (hh' := Memℓp.finsetSum T (fun i _ => hf i)) hfun hsub
  exact hasFreqSupport_mono hunion hmid

/-- **The frequency support of a shifted major-arc function.**  If every `f δ` is band-limited in
the arc `arcSet δ ε`, then the shifted major-arc function
`f_{Σ_{A₀} + α₀} = Σ_{γ ∈ Σ_{A₀}} f_{γ + α₀}` has frequency support in the shifted arc
`Σ_{⊆A₀} + α₀ + [-ε,ε]`. -/
theorem hasFreqSupport_majorArc_shift {A₀ : Finset ℕ} {f : Circle → ℤ → ℂ}
    (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε)) (α₀ : Circle) :
    HasFreqSupport (fun m => ∑ γ ∈ sigmaAFinset A₀, f (γ + α₀) m)
      (Memℓp.finsetSum (sigmaAFinset A₀) (fun γ _ => hf (γ + α₀)))
      (shiftArcSet (sigmaSubA A₀) α₀ ε) := by
  refine hasFreqSupport_mono ?_ (hasFreqSupport_finsetSum (sigmaAFinset A₀)
    (f := fun γ => f (γ + α₀)) (hf := fun γ => hf (γ + α₀))
    (E := fun γ => arcSet (γ + α₀) ε) (hE := fun γ => hF (γ + α₀)))
  rintro ξ hmem
  rw [Set.mem_iUnion] at hmem
  obtain ⟨γ, hmem⟩ := hmem
  rw [Set.mem_iUnion] at hmem
  obtain ⟨hγ, hmem⟩ := hmem
  rw [arcSet] at hmem
  obtain ⟨θ, hθ, hξ⟩ := hmem
  exact ⟨γ, sigmaAFinset_subset_sigmaSubA A₀ hγ, θ, hθ, hξ⟩

end Work.BourgainPlan.IonescuWainger

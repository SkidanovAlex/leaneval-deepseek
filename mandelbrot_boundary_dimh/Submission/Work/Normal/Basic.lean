import Mathlib

/-!
# Normal families, Fatou and Julia sets

This file sets up the vocabulary of complex dynamics used by the mandelbar
(`Submission/Work/Normal/`) area of the project.  Nothing here is specific to the
tricorn: everything is stated for a self-map `f : ℂ → ℂ` of the plane.

Conventions (following Milnor, *Dynamics in one complex variable*, chapter 4):

* `TendstoLocallyUniformlyAtTop F U` : the sequence `F` tends to the constant `∞`
  locally uniformly on `U`.
* `IsNormalFamily Fam U` : every sequence of members of `Fam` has a subsequence which
  converges locally uniformly on `U`, either to a limit function on `U` or to the
  constant `∞` (equivalently: `Fam` is relatively compact in the space of continuous
  maps `U → ℂ̂` for the compact open topology).
* `FatouSet f` : the set of points `z` having an open neighbourhood on which the family
  of iterates `{f^[n]}` is normal.
* `JuliaSet f` : the complement of `FatouSet f`.
* `FilledJuliaSet f` : the set of points whose orbit under `f` is bounded.

The main results of this area live in the modules
`Submission.Work.Normal.montel_locallyBounded` (Montel's theorem for locally bounded
families of holomorphic functions),
`Submission.Work.Normal.montel_omits_three` (Montel's three-omitted-values theorem),
and the modules listed in `Submission/Work/Normal/NOTES.md`.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

/-- A sequence of functions tends to `∞` locally uniformly on `U` if for every compact
`K ⊆ U` and every real `R`, eventually `R ≤ ‖F n z‖` for every `z ∈ K`. -/
def TendstoLocallyUniformlyAtTop (F : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ K, R ≤ ‖F n z‖

/-- A family of functions is **normal** on `U` if every sequence of members of the family
has a subsequence which converges locally uniformly on `U`, either to a limit function on
`U` (which is holomorphic when the members are) or to the constant `∞`. -/
def IsNormalFamily (Fam : Set (ℂ → ℂ)) (U : Set ℂ) : Prop :=
  ∀ u : ℕ → ℂ → ℂ, (∀ n, u n ∈ Fam) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n => u (φ n)) g atTop U) ∨
        TendstoLocallyUniformlyAtTop (fun n => u (φ n)) U)

/-- A family of functions is locally bounded on `U` if it is uniformly bounded on every
compact subset of `U`. -/
def IsLocallyBoundedOn (Fam : Set (ℂ → ℂ)) (U : Set ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ f ∈ Fam, ∀ z ∈ K, ‖f z‖ ≤ M

/-- The family of iterates of `f`. -/
def iterateFamily (f : ℂ → ℂ) : Set (ℂ → ℂ) := Set.range (fun n : ℕ => f^[n])

/-- The **Fatou set** of `f`: the points having an open neighbourhood on which the family
of iterates of `f` is normal. -/
def FatouSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ U : Set ℂ, U ∈ 𝓝 z ∧ IsOpen U ∧ IsNormalFamily (iterateFamily f) U}

/-- The **Julia set** of `f`, the complement of the Fatou set. -/
def JuliaSet (f : ℂ → ℂ) : Set ℂ := (FatouSet f)ᶜ

/-- The **filled Julia set** of `f`: the set of points whose orbit under `f` is bounded.
For a polynomial this is the set usually denoted `K(f)`. -/
def FilledJuliaSet (f : ℂ → ℂ) : Set ℂ := {z | ∃ M : ℝ, ∀ n : ℕ, ‖f^[n] z‖ ≤ M}

/-- `f` is the evaluation map of a polynomial of (natural) degree `d`. -/
def IsPolynomialMapOfDegree (d : ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ P : ℂ[X], P.natDegree = d ∧ ∀ z, f z = P.eval z

/-- A continuous map of the plane which tends to infinity at infinity: `‖e z‖ → ∞` as
`‖z‖ → ∞`.  This holds for every nonconstant polynomial map, and also for every antiholomorphic
quadratic map `z ↦ (conj z)^2 + c`; it is exactly what is needed for the composition of a
`TendstoLocallyUniformlyAtTop` sequence with `e` to still tend to `∞`. -/
def IsCoerciveContinuous (e : ℂ → ℂ) : Prop :=
  Continuous e ∧ ∀ R : ℝ, ∃ S : ℝ, ∀ z : ℂ, S ≤ ‖z‖ → R ≤ ‖e z‖

/-- `f` is the evaluation map of a polynomial of degree at least `2`. -/
def IsPolynomialMapOfDegreeAtLeastTwo (f : ℂ → ℂ) : Prop :=
  ∃ P : ℂ[X], 2 ≤ P.natDegree ∧ ∀ z, f z = P.eval z

variable {f g : ℂ → ℂ} {U V K : Set ℂ} {Fam Fam' : Set (ℂ → ℂ)}

/-! ### Elementary API for normality -/

theorem IsNormalFamily.mono (h : IsNormalFamily Fam U) (hVU : V ⊆ U) :
    IsNormalFamily Fam V := by
  intro u hu
  obtain ⟨φ, hφ, hlim | hlim⟩ := h u hu
  · exact ⟨φ, hφ, Or.inl (hlim.imp fun g hg => hg.mono hVU)⟩
  · refine ⟨φ, hφ, Or.inr ?_⟩
    intro K hKV hK R
    exact hlim K (hKV.trans hVU) hK R

theorem IsLocallyBoundedOn.mono (h : IsLocallyBoundedOn Fam U) (hVU : V ⊆ U) :
    IsLocallyBoundedOn Fam V :=
  fun K hKV hK => h K (hKV.trans hVU) hK

theorem IsLocallyBoundedOn.mono_family (h : IsLocallyBoundedOn Fam U) (hF : Fam' ⊆ Fam) :
    IsLocallyBoundedOn Fam' U :=
  fun K hKU hK => let ⟨M, hM⟩ := h K hKU hK; ⟨M, fun f hf z hz => hM f (hF hf) z hz⟩

theorem IsNormalFamily.mono_family (h : IsNormalFamily Fam U) (hF : Fam' ⊆ Fam) :
    IsNormalFamily Fam' U := by
  intro u hu
  exact h u fun n => hF (hu n)

/-! ### Elementary API for the Fatou and Julia sets -/

theorem fatouSet_compl (f : ℂ → ℂ) : (FatouSet f)ᶜ = JuliaSet f := rfl

theorem juliaSet_compl (f : ℂ → ℂ) : (JuliaSet f)ᶜ = FatouSet f := compl_compl _

theorem mem_juliaSet {z : ℂ} :
    z ∈ JuliaSet f ↔ ¬ ∃ U : Set ℂ, U ∈ 𝓝 z ∧ IsOpen U ∧ IsNormalFamily (iterateFamily f) U :=
  Iff.rfl

theorem fatouSet_of_mem_nhds {z : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 z) (hUo : IsOpen U)
    (h : IsNormalFamily (iterateFamily f) U) : z ∈ FatouSet f := ⟨U, hU, hUo, h⟩

theorem isOpen_fatouSet (f : ℂ → ℂ) : IsOpen (FatouSet f) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hUo, hnorm⟩
  exact mem_of_superset hU fun w hw => ⟨U, hUo.mem_nhds hw, hUo, hnorm⟩

theorem isClosed_juliaSet (f : ℂ → ℂ) : IsClosed (JuliaSet f) :=
  (isOpen_fatouSet f).isClosed_compl

theorem apply_mem_iterateFamily (f : ℂ → ℂ) (n : ℕ) : f^[n] ∈ iterateFamily f :=
  ⟨n, rfl⟩

/-! ### Invariance of the filled Julia set -/

theorem mapsTo_filledJuliaSet (f : ℂ → ℂ) : MapsTo f (FilledJuliaSet f) (FilledJuliaSet f) := by
  rintro z ⟨M, hM⟩
  refine ⟨M, fun n => ?_⟩
  rw [← Function.iterate_succ_apply]
  exact hM (n + 1)

theorem preimage_filledJuliaSet_subset (f : ℂ → ℂ) :
    f ⁻¹' (FilledJuliaSet f) ⊆ FilledJuliaSet f := by
  rintro z hz
  obtain ⟨M, hM⟩ := hz
  refine ⟨max M ‖z‖, fun n => ?_⟩
  cases n with
  | zero => simpa using le_max_right M ‖z‖
  | succ n => rw [Function.iterate_succ_apply]; exact (hM n).trans (le_max_left M ‖z‖)

end Work.Normal

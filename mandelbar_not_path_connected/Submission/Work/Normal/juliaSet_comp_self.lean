import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Julia set of a coercive continuous map equals that of its square

For a self-map `f` of the plane the Julia set is defined purely in terms of normal families
(no differentiability is used): `JuliaSet f = (FatouSet f)ᶜ`, where `z ∈ FatouSet f` if some
open neighbourhood of `z` carries a normal family of iterates of `f`.

The iterates of `f ∘ f` are the **even** iterates of `f` (`(f ∘ f)^[n] = f^[2 n]`), so the
family of iterates of `f ∘ f` is a subfamily of the family of iterates of `f`; this gives
`JuliaSet (f ∘ f) ⊆ JuliaSet f` with no hypothesis at all (normality passes to subfamilies).

Conversely the **odd** iterates are `f^[2 n + 1] = f ∘ f^[2 n]`, i.e. they are the even iterates
post-composed with `f`.  If the even iterates form a normal family and if `f` is *coercive*
continuous (`‖f z‖ → ∞` as `‖z‖ → ∞`), then so do the odd ones:

* along a subsequence whose limit is a genuine function `g`, the continuity of `g` (a locally
  uniform limit of continuous functions) together with the continuity of `f` gives locally uniform
  convergence of `f ∘ f^[2 n]` to `f ∘ g`;
* along a subsequence tending to `∞` locally uniformly, coercivity of `f` transports the limit
  `∞`.

A sequence of iterates of `f` is a mixture of even and odd ones, and any sequence contained in a
union of two families one of whose sets contains infinitely many of its terms has a subsequence
contained in one of them (`exists_strictMono_forall_mem_of_forall_mem_union`).  Hence normality
of the even and of the odd family implies normality of the family of all iterates of `f`, giving
`JuliaSet f ⊆ JuliaSet (f ∘ f)`.

The hypothesis `IsCoerciveContinuous` holds for every nonconstant polynomial map and for the
antiholomorphic quadratic maps `z ↦ (conj z)^2 + c`; for those, `e ∘ e` is the holomorphic map
`z ↦ (z^2 + conj c)^2 + c`, so the result identifies the Julia set of the antiholomorphic map
with that of its holomorphic second iterate.
-/

namespace Work.Normal

open Set Filter Topology Function Metric
open scoped Topology

/-! ### Iterates of `f ∘ f` versus iterates of `f` -/

/-- The iterates of `f ∘ f` are the even iterates of `f`. -/
theorem iterate_comp_self_eq_two_mul {f : ℂ → ℂ} (n : ℕ) : (f ∘ f)^[n] = f^[2 * n] := by
  have h2 : f^[2] = f ∘ f := by rw [Function.iterate_succ', Function.iterate_one]
  calc (f ∘ f)^[n] = (f^[2])^[n] := by rw [h2]
    _ = f^[2 * n] := (Function.iterate_mul f 2 n).symm

/-- Every natural number is either twice something or one more than twice something. -/
theorem exists_two_mul_eq_or_two_mul_add_one (k : ℕ) :
    (∃ m, k = 2 * m) ∨ ∃ m, k = 2 * m + 1 := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl ⟨m, by omega⟩
  · exact Or.inr ⟨m, by omega⟩

/-! ### Normal families and finite unions -/

/-- A sequence of an arbitrary type taking its values in a union `A ∪ B` has a strictly monotone
subsequence taking its values in `A`, or one taking its values in `B`. -/
theorem exists_strictMono_forall_mem_of_forall_mem_union {α : Type*} {A B : Set α} {u : ℕ → α}
    (h : ∀ n, u n ∈ A ∪ B) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) ∈ A) ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) ∈ B := by
  by_cases hA : ∃ᶠ n in atTop, u n ∈ A
  · obtain ⟨φ, hφ, hmem⟩ := Filter.extraction_of_frequently_atTop hA
    exact Or.inl ⟨φ, hφ, hmem⟩
  · rw [Filter.not_frequently] at hA
    obtain ⟨φ, hφ, hmem⟩ := Filter.extraction_of_eventually_atTop hA
    refine Or.inr ⟨φ, hφ, fun n => ?_⟩
    rcases h (φ n) with h1 | h2
    · exact absurd h1 (hmem n)
    · exact h2

/-- A finite union of normal families is normal: a sequence in `A ∪ B` has a strictly monotone
subsequence lying in `A` or one lying in `B` (`exists_strictMono_forall_mem_of_forall_mem_union`),
and normality applies to that subsequence. -/
theorem isNormalFamily_union {A B : Set (ℂ → ℂ)} {U : Set ℂ} (hA : IsNormalFamily A U)
    (hB : IsNormalFamily B U) : IsNormalFamily (A ∪ B) U := by
  intro u hu
  rcases exists_strictMono_forall_mem_of_forall_mem_union hu with ⟨φ, hφ, hA'⟩ | ⟨φ, hφ, hB'⟩
  · obtain ⟨σ, hσ, hlim⟩ := hA (fun n => u (φ n)) hA'
    exact ⟨φ ∘ σ, hφ.comp hσ, hlim⟩
  · obtain ⟨σ, hσ, hlim⟩ := hB (fun n => u (φ n)) hB'
    exact ⟨φ ∘ σ, hφ.comp hσ, hlim⟩

/-! ### Post-composition with a continuous coercive map -/

/-- Post-composing a locally uniformly `∞`-divergent sequence with a coercive continuous map keeps
it locally uniformly divergent.  (Only coercivity is used; continuity is not needed here.) -/
theorem TendstoLocallyUniformlyAtTop.comp_isCoercive {u : ℕ → ℂ → ℂ} {U : Set ℂ} {e : ℂ → ℂ}
    (he : IsCoerciveContinuous e) (hu : TendstoLocallyUniformlyAtTop u U) :
    TendstoLocallyUniformlyAtTop (fun n => e ∘ u n) U := by
  intro K hKU hK R
  obtain ⟨S, hS⟩ := he.2 R
  obtain ⟨n₀, hn₀⟩ := hu K hKU hK S
  exact ⟨n₀, fun n hn z hz => hS (u n z) (hn₀ n hn z hz)⟩

/-- Post-composing a locally uniformly convergent sequence with a continuous map preserves local
uniform convergence, provided the limit function is continuous on the set in question.  (This is
automatic in the intended applications, where `g` is a locally uniform limit of continuous
functions and `U` is open.)  On each compact `K ⊆ U` one reduces to `TendstoUniformlyOn`, where
the values of `g` on `K` form a compact set on which `e` is uniformly continuous. -/
theorem tendstoLocallyUniformlyOn_comp_continuousOn {u : ℕ → ℂ → ℂ}
    {g e : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (he : Continuous e) (hg : ContinuousOn g U)
    (hu : TendstoLocallyUniformlyOn u g atTop U) :
    TendstoLocallyUniformlyOn (fun n => e ∘ u n) (e ∘ g) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at hu ⊢
  intro K hKU hK
  have huK : TendstoUniformlyOn u g atTop K := hu K hKU hK
  have hgK : ContinuousOn g K := hg.mono hKU
  have hcomp : IsCompact (g '' K) := hK.image_of_continuousOn hgK
  -- `e` is uniformly continuous on the compact thickening of the values of `g` on `K`
  have huct : UniformContinuousOn e (Metric.cthickening 1 (g '' K)) :=
    (hcomp.cthickening).uniformContinuousOn_of_continuous he.continuousOn
  have hFK : ∀ᶠ n in atTop, ∀ x ∈ K, u n x ∈ Metric.cthickening 1 (g '' K) := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp huK) 1 one_pos] with n hn x hx
    refine Metric.mem_cthickening_of_dist_le (u n x) (g x) 1 (g '' K) ⟨x, hx, rfl⟩ ?_
    rw [dist_comm]; exact le_of_lt (hn x hx)
  have hgK' : ∀ x ∈ K, g x ∈ Metric.cthickening 1 (g '' K) :=
    fun x hx => Metric.self_subset_cthickening _ ⟨x, hx, rfl⟩
  simpa only [Function.comp_def] using huct.comp_tendstoUniformlyOn_eventually hFK hgK' huK

/-- If `Fam` is a normal family of continuous functions and `e` is coercive continuous, then the
family of post-compositions `e ∘ f`, `f ∈ Fam`, is again normal: a sequence of such compositions
comes from a sequence in `Fam`, to which normality applies; then use `TendstoLocallyUniformlyOn`
`.comp_continuousOn` in the function-limit case and `TendstoLocallyUniformlyAtTop.comp_isCoercive`
in the `∞`-limit case. -/
theorem isNormalFamily_image_comp {Fam : Set (ℂ → ℂ)} {U : Set ℂ} {e : ℂ → ℂ}
    (he : IsCoerciveContinuous e) (hUo : IsOpen U) (hcont : ∀ f ∈ Fam, Continuous f)
    (hFam : IsNormalFamily Fam U) :
    IsNormalFamily ((fun f => e ∘ f) '' Fam) U := by
  intro u hu
  choose v hv hv_eq using fun n => (Set.mem_image (fun f => e ∘ f) Fam (u n)).mp (hu n)
  obtain ⟨φ, hφ, hlim | htla⟩ := hFam v hv
  · obtain ⟨g, hg⟩ := hlim
    -- the limit of continuous functions is continuous
    have hgc : ContinuousOn g U :=
      hg.continuousOn (Filter.Eventually.of_forall fun n => (hcont _ (hv _)).continuousOn).frequently
    refine ⟨φ, hφ, Or.inl ⟨e ∘ g, ?_⟩⟩
    have h1 := tendstoLocallyUniformlyOn_comp_continuousOn hUo he.1 hgc hg
    rwa [show (fun n => e ∘ v (φ n)) = (fun n => u (φ n)) from funext fun n => hv_eq (φ n)] at h1
  · refine ⟨φ, hφ, Or.inr ?_⟩
    have h2 := TendstoLocallyUniformlyAtTop.comp_isCoercive he htla
    rwa [show (fun n => e ∘ v (φ n)) = (fun n => u (φ n)) from funext fun n => hv_eq (φ n)] at h2

/-! ### The Julia set of `e ∘ e` -/

/-- A coercive continuous map of the plane has the same Julia set as its square.  The even
iterates of `e` are the iterates of `e ∘ e`, and the odd iterates are `e` composed with an even
iterate; post-composition with the coercive continuous `e` preserves local uniform convergence
(and the limit `∞`).  This applies in particular to the antiholomorphic quadratic maps
`z ↦ (conj z)^2 + c`, where it identifies the Julia set of the antiholomorphic map with that of
its holomorphic second iterate `z ↦ (z^2 + conj c)^2 + c`. -/
theorem juliaSet_comp_self {e : ℂ → ℂ} (he : IsCoerciveContinuous e) :
    JuliaSet (e ∘ e) = JuliaSet e := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · -- the iterates of `e ∘ e` are a subfamily of the iterates of `e`
    intro z hz
    rw [JuliaSet, Set.mem_compl_iff] at hz ⊢
    intro hze
    obtain ⟨U, hUmem, hUo, hnorm⟩ := hze
    exact hz ⟨U, hUmem, hUo, hnorm.mono_family fun f hf => by
      obtain ⟨n, rfl⟩ := hf
      exact ⟨2 * n, (iterate_comp_self_eq_two_mul n).symm⟩⟩
  · -- the iterates of `e` are the even iterates together with the odd ones
    intro z hz
    rw [JuliaSet, Set.mem_compl_iff] at hz ⊢
    intro hz2
    obtain ⟨U, hUmem, hUo, hnorm⟩ := hz2
    have hc : Continuous e := he.1
    have hcont : ∀ f ∈ Set.range (fun n : ℕ => e^[2 * n]), Continuous f := by
      rintro f ⟨n, rfl⟩
      exact hc.iterate (2 * n)
    -- the even iterates of `e` are the iterates of `e ∘ e`, hence normal
    have heven : IsNormalFamily (Set.range (fun n : ℕ => e^[2 * n])) U :=
      hnorm.mono_family fun f hf => by
        obtain ⟨n, rfl⟩ := hf
        exact ⟨n, iterate_comp_self_eq_two_mul n⟩
    -- the odd iterates of `e` are `e` composed with an even iterate, hence normal
    have hodd : IsNormalFamily ((fun f => e ∘ f) '' Set.range (fun n : ℕ => e^[2 * n])) U :=
      isNormalFamily_image_comp he hUo hcont heven
    have hunion := isNormalFamily_union heven hodd
    exact hz ⟨U, hUmem, hUo, hunion.mono_family fun f hf => by
      obtain ⟨k, rfl⟩ := hf
      rcases exists_two_mul_eq_or_two_mul_add_one k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact Or.inl ⟨m, rfl⟩
      · refine Or.inr ⟨e^[2 * m], ⟨m, rfl⟩, ?_⟩
        funext z
        exact (Function.iterate_succ_apply' e (2 * m) z).symm⟩

end Work.Normal

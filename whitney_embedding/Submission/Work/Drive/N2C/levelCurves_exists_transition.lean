import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2C.isotopyCalc
import Submission.Work.Drive.N2C.levelCurves_componentMatch

/-!
# `N2C` B6: two parametrisations of a regular level are matched by a reparametrisation

Two `LevelCurves` parametrisations of the same regular level differ by a bijection of the components
and, componentwise, by a smooth `1`-periodic-up-to-`±1` reparametrisation of the circle with
nowhere-vanishing derivative of the matching sign.

The proof is in four parts: the components are matched (`levelCurves_componentMatch`); the curve
`L'.γ i` is lifted through `L.γ (σ i)` by the covering-space lifting theorem for the covering
`ℝ → AddCircle (1:ℝ)` (which both curves factor through, by periodicity); the integer shift of the
lift is `±1` by composing the lifts in both directions; and the resulting monotone reparametrisation
is smooth by the inverse function theorem in a chart, which also gives the sign of its derivative.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

/-- A nonzero linear functional on `ℝ²` has a nonzero kernel vector. -/
theorem lvcrep_exists_ne_zero_ker_e2 (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧ A v = 0 := by
  by_cases h : A (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 0
  · refine ⟨EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_, h⟩
    intro hz
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v.ofLp 0) hz
    simpa using h1
  · refine ⟨EuclideanSpace.single (1 : Fin 2) (1 : ℝ) -
      (A (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) /
        A (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) •
        EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_, ?_⟩
    · intro hz
      have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v.ofLp 1) hz
      simp at h1
    · have h' : (A (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) /
          A (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) •
            A (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
          = A (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
        rw [smul_eq_mul, div_mul_cancel₀ _ h]
      rw [map_sub, map_smul, h', sub_self]

/-- **The parametrising curves of a level are immersions**: the `ker` row of `LevelCurves` identifies
the range of `mfderiv γ t` with `ker (mfderiv f (γ t))`, and the latter is nonzero (there is a
nonzero kernel vector by `lvcrep_exists_ne_zero_ker_e2`). -/
theorem lvcrep_mfderiv_ne_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (L : LevelCurves f b n) (i : Fin n) (t : ℝ) :
    mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (L.γ i) t ≠ 0 := by
  intro hzero
  have h1 : (mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (L.γ i) t) 1 = 0 := by
    rw [hzero]; rfl
  obtain ⟨v, hvne, hv0⟩ := lvcrep_exists_ne_zero_ker_e2 (mfderiv
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) f (L.γ i t))
  obtain ⟨s, hs⟩ := L.ker i t v hv0
  have hsa : s • (1 : TangentSpace (modelWithCornersSelf ℝ ℝ) t) = s := by
    show s * 1 = s
    ring
  have hs0 : (mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (L.γ i) t) s = 0 := by
    conv_lhs => rw [← hsa, ContinuousLinearMap.map_smul]
    rw [h1, smul_zero]
  rw [hs] at hs0
  exact hvne hs0

/-- **A continuous integer-valued function on `ℝ` is constant**: the fibre of its value at `0` is
clopen (closed by continuity, open because two distinct integers differ by at least `1`), hence all
of `ℝ` by preconnectedness. -/
theorem lvcrep_exists_int_const_of_continuous_int {g : ℝ → ℝ} (hg : Continuous g)
    (hint : ∀ x, ∃ k : ℤ, g x = k) : ∃ k : ℤ, ∀ x, g x = k := by
  obtain ⟨k₀, hk₀⟩ := hint 0
  refine ⟨k₀, fun x => ?_⟩
  have hopen : IsOpen (g ⁻¹' {(k₀ : ℝ)}) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hmem : Set.Ioo ((k₀ : ℝ) - 1) ((k₀ : ℝ) + 1) ∈ 𝓝 (g x) := by
      rw [hx]
      exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    refine Filter.mem_of_superset (hg.continuousAt.preimage_mem_nhds hmem) ?_
    intro y hy
    simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_singleton_iff] at hy ⊢
    obtain ⟨k, hk⟩ := hint y
    have hy' : (k : ℝ) ∈ Set.Ioo ((k₀ : ℝ) - 1) ((k₀ : ℝ) + 1) := by rw [← hk]; exact hy
    have h1 : |((k - k₀ : ℤ) : ℝ)| < 1 := by
      push_cast
      rw [abs_lt]
      exact ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
    have h2 : k - k₀ = 0 := by
      have h3 := abs_lt.mp h1
      have h4 : (-1 : ℤ) < k - k₀ := by exact_mod_cast h3.1
      have h5 : k - k₀ < (1 : ℤ) := by exact_mod_cast h3.2
      omega
    rw [hk]
    exact_mod_cast (show k = k₀ by omega)
  have hcl : IsClosed (g ⁻¹' {(k₀ : ℝ)}) := isClosed_singleton.preimage hg
  have hsub : Set.univ ⊆ g ⁻¹' {(k₀ : ℝ)} :=
    isPreconnected_univ.subset_isClopen ⟨hcl, hopen⟩ ⟨0, by simpa using hk₀⟩
  exact hsub (Set.mem_univ x)

/-- **Iterating an integer shift**: if `h (x + 1) = h x + k` then `h (x + n) = h x + n * k`.  Pass to
the `1`-periodic function `z ↦ h z - k * z`. -/
theorem lvcrep_shift_int_apply {h : ℝ → ℝ} {k : ℝ} (hk : ∀ x, h (x + 1) = h x + k)
    (n : ℤ) (x : ℝ) : h (x + (n : ℝ)) = h x + (n : ℝ) * k := by
  have hper : Function.Periodic (fun z : ℝ => h z - k * z) (1:ℝ) := by
    intro z
    show h (z + 1) - k * (z + 1) = h z - k * z
    rw [hk z]; ring
  have h1 : h (x + (n:ℝ)) - k * (x + (n:ℝ)) = h x - k * x := by
    simpa using (hper.int_mul n) x
  linarith

/-- **The lift of a reparametrisation through a covering of the circle.**  Two continuous
`1`-periodic curves of a Hausdorff space with the same range, the first one injective modulo `ℤ`,
satisfy `β = α ∘ h` for a continuous `h : ℝ → ℝ`.  Both factor through `AddCircle (1:ℝ)` and the
factorisations are homeomorphisms onto the common compact range; the composite is lifted along the
covering `ℝ → AddCircle (1:ℝ)`. -/
theorem lvcrep_exists_continuous_lift_of_range_eq {M : Type*} [TopologicalSpace M] [T2Space M]
    {α β : ℝ → M}
    (hαc : Continuous α) (hβc : Continuous β)
    (hαper : ∀ x : ℝ, α (x + 1) = α x)
    (hβper : ∀ x : ℝ, β (x + 1) = β x)
    (hαmod : ∀ x y : ℝ, α x = α y → ∃ k : ℤ, x = y + k)
    (hrange : Set.range β = Set.range α) :
    ∃ h : ℝ → ℝ, Continuous h ∧ ∀ x : ℝ, β x = α (h x) := by
  classical
  have hα01 : α 0 = α 1 := by simpa using (hαper 0).symm
  have hβ01 : β 0 = β 1 := by simpa using (hβper 0).symm
  let A : AddCircle (1:ℝ) → M := AddCircle.liftIco 1 0 α
  let B : AddCircle (1:ℝ) → M := AddCircle.liftIco 1 0 β
  have hAc : Continuous A := AddCircle.liftIco_zero_continuous (p := (1:ℝ)) hα01 hαc.continuousOn
  have hBc : Continuous B := AddCircle.liftIco_zero_continuous (p := (1:ℝ)) hβ01 hβc.continuousOn
  have hαint : ∀ (a : ℝ) (k : ℤ), α (a + (k:ℝ)) = α a := by
    intro a k
    have h := Function.Periodic.int_mul (hαper : Function.Periodic α (1:ℝ)) k a
    simpa using h
  have hβint : ∀ (a : ℝ) (k : ℤ), β (a + (k:ℝ)) = β a := by
    intro a k
    have h := Function.Periodic.int_mul (hβper : Function.Periodic β (1:ℝ)) k a
    simpa using h
  have hAcc : ∀ y : ℝ, A (↑y : AddCircle (1:ℝ)) = α y := by
    intro y
    have hy : y = Int.fract y + (⌊y⌋ : ℝ) := by linarith [Int.self_sub_floor (R := ℝ) y]
    show AddCircle.liftIco 1 0 α (↑y) = α y
    rw [← AddCircle.coe_fract y]
    rw [AddCircle.liftIco_zero_coe_apply (p := (1:ℝ)) ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩]
    conv_rhs => rw [hy]
    exact (hαint (Int.fract y) ⌊y⌋).symm
  have hBcc : ∀ y : ℝ, B (↑y : AddCircle (1:ℝ)) = β y := by
    intro y
    have hy : y = Int.fract y + (⌊y⌋ : ℝ) := by linarith [Int.self_sub_floor (R := ℝ) y]
    show AddCircle.liftIco 1 0 β (↑y) = β y
    rw [← AddCircle.coe_fract y]
    rw [AddCircle.liftIco_zero_coe_apply (p := (1:ℝ)) ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩]
    conv_rhs => rw [hy]
    exact (hβint (Int.fract y) ⌊y⌋).symm
  let rep : AddCircle (1:ℝ) → ℝ :=
    fun u => ((AddCircle.equivIco (1:ℝ) 0 u : Set.Ico (0:ℝ) (0+1)) : ℝ)
  have hrep_coe : ∀ u : AddCircle (1:ℝ), (rep u : AddCircle (1:ℝ)) = u := by
    intro u; exact AddCircle.coe_equivIco ..
  have hrep_mem : ∀ u : AddCircle (1:ℝ), rep u ∈ Set.Ico (0:ℝ) 1 := by
    intro u; simpa [rep] using (AddCircle.equivIco (1:ℝ) 0 u).2
  have hrep_A : ∀ u : AddCircle (1:ℝ), A u = α (rep u) := by
    intro u
    have h := hAcc (rep u)
    rw [hrep_coe u] at h
    exact h
  have hrep_B : ∀ u : AddCircle (1:ℝ), B u = β (rep u) := by
    intro u
    have h := hBcc (rep u)
    rw [hrep_coe u] at h
    exact h
  have hAinj : Function.Injective A := by
    intro u v huv
    have hαeq : α (rep u) = α (rep v) := by rw [← hrep_A u, ← hrep_A v, huv]
    obtain ⟨k, hk⟩ := hαmod (rep u) (rep v) hαeq
    have hk1 : (k:ℝ) < 1 := by
      linarith [(hrep_mem u).1, (hrep_mem u).2, (hrep_mem v).1, (hrep_mem v).2, hk]
    have hk2 : (-1:ℝ) < (k:ℝ) := by
      linarith [(hrep_mem u).1, (hrep_mem u).2, (hrep_mem v).1, (hrep_mem v).2, hk]
    have hklt : k < 1 := by exact_mod_cast hk1
    have hkgt : -1 < k := by exact_mod_cast hk2
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    simp only [Int.cast_zero, add_zero] at hk
    rw [← hrep_coe u, ← hrep_coe v, hk]
  have hA_range : ∀ u : AddCircle (1:ℝ), A u ∈ Set.range α := fun u => ⟨rep u, (hrep_A u).symm⟩
  have hB_range : ∀ u : AddCircle (1:ℝ), B u ∈ Set.range β := fun u => ⟨rep u, (hrep_B u).symm⟩
  let A' : AddCircle (1:ℝ) → Set.range α := fun u => ⟨A u, hA_range u⟩
  have hA'c : Continuous A' := hAc.subtype_mk _
  have hA'bij : Function.Bijective A' := by
    constructor
    · intro u v huv
      exact hAinj (Subtype.ext_iff.mp huv)
    · intro z
      obtain ⟨y, hy⟩ := z.2
      refine ⟨(y : AddCircle (1:ℝ)), ?_⟩
      refine Subtype.ext ?_
      rw [show (A' (↑y) : M) = A ↑y from rfl, hAcc y, hy]
  let eA : AddCircle (1:ℝ) ≃ₜ Set.range α :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective A' hA'bij) hA'c
  let B₂ : AddCircle (1:ℝ) → Set.range α := fun u => ⟨B u, by rw [← hrange]; exact hB_range u⟩
  have hB₂c : Continuous B₂ := hBc.subtype_mk _
  let κ : AddCircle (1:ℝ) → AddCircle (1:ℝ) := fun u => eA.symm (B₂ u)
  have hκc : Continuous κ := eA.continuous_symm.comp hB₂c
  have hκq : Continuous (fun x : ℝ => κ (↑x : AddCircle (1:ℝ))) :=
    hκc.comp QuotientAddGroup.continuous_mk
  have hcov : IsCoveringMap ((↑) : ℝ → AddCircle (1:ℝ)) := AddCircle.isCoveringMap_coe (1:ℝ)
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℝ, (e₀ : AddCircle (1:ℝ)) = κ 0 :=
    ⟨((AddCircle.equivIco (1:ℝ) 0 (κ 0) : Set.Ico (0:ℝ) (0+1)) : ℝ), AddCircle.coe_equivIco ..⟩
  obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (⟨fun x : ℝ => κ (↑x), hκq⟩) 0 e₀ (by simpa using he₀)
  refine ⟨fun x => (F x : ℝ), F.continuous, ?_⟩
  intro x
  have hFx : ((F x : ℝ) : AddCircle (1:ℝ)) = κ (↑x) := congrFun hFlift x
  calc β x = B (↑x : AddCircle (1:ℝ)) := (hBcc x).symm
    _ = (B₂ (↑x) : M) := rfl
    _ = (eA (κ (↑x)) : M) := by rw [Homeomorph.apply_symm_apply]
    _ = A (κ (↑x)) := rfl
    _ = A (↑(F x) : AddCircle (1:ℝ)) := by rw [hFx]
    _ = α (F x) := hAcc (F x)

/-- **The shift of a lifted reparametrisation is `± 1`.**  Lifting in both directions and composing
gives continuous `h, h'` with `β = α ∘ h`, `α = β ∘ h'` and shifts `k`, `k'`; the continuous
integer-valued function `x ↦ h' (h x) - x` is constant (`c`), and `k * k' = 1` follows by evaluating
`h' (h (x + 1))` two ways at `x = 0`. -/
theorem lvcrep_exists_lift_shift_pm_one {M : Type*} [TopologicalSpace M] [T2Space M]
    {α β : ℝ → M}
    (hαc : Continuous α) (hβc : Continuous β)
    (hαper : ∀ x : ℝ, α (x + 1) = α x)
    (hβper : ∀ x : ℝ, β (x + 1) = β x)
    (hαmod : ∀ x y : ℝ, α x = α y → ∃ k : ℤ, x = y + k)
    (hβmod : ∀ x y : ℝ, β x = β y → ∃ k : ℤ, x = y + k)
    (hrange : Set.range β = Set.range α) :
    ∃ (h : ℝ → ℝ) (k : ℤ), Continuous h ∧ (k = 1 ∨ k = -1) ∧
      (∀ x : ℝ, h (x + 1) = h x + (k : ℝ)) ∧ (∀ x : ℝ, β x = α (h x)) := by
  obtain ⟨h, hhc, hhe⟩ :=
    lvcrep_exists_continuous_lift_of_range_eq hαc hβc hαper hβper hαmod hrange
  obtain ⟨h', h'hc, h'he⟩ :=
    lvcrep_exists_continuous_lift_of_range_eq hβc hαc hβper hαper hβmod hrange.symm
  have hkex : ∃ k : ℤ, ∀ x : ℝ, h (x + 1) = h x + (k : ℝ) := by
    have hcont' : Continuous (fun x : ℝ => h (x + 1) - h x) :=
      (hhc.comp (continuous_id.add continuous_const)).sub hhc
    have hint : ∀ x : ℝ, ∃ k : ℤ, h (x + 1) - h x = (k : ℝ) := by
      intro x
      have he : α (h (x + 1)) = α (h x) := by rw [← hhe (x + 1), ← hhe x, hβper x]
      obtain ⟨j, hj⟩ := hαmod (h (x + 1)) (h x) he
      exact ⟨j, by rw [hj]; ring⟩
    obtain ⟨k, hk⟩ := lvcrep_exists_int_const_of_continuous_int hcont' hint
    exact ⟨k, fun x => by have := hk x; linarith⟩
  obtain ⟨k, hk⟩ := hkex
  have hk'ex : ∃ k' : ℤ, ∀ x : ℝ, h' (x + 1) = h' x + (k' : ℝ) := by
    have hcont' : Continuous (fun x : ℝ => h' (x + 1) - h' x) :=
      (h'hc.comp (continuous_id.add continuous_const)).sub h'hc
    have hint : ∀ x : ℝ, ∃ k : ℤ, h' (x + 1) - h' x = (k : ℝ) := by
      intro x
      have he : β (h' (x + 1)) = β (h' x) := by rw [← h'he (x + 1), ← h'he x, hαper x]
      obtain ⟨j, hj⟩ := hβmod (h' (x + 1)) (h' x) he
      exact ⟨j, by rw [hj]; ring⟩
    obtain ⟨k', hk'⟩ := lvcrep_exists_int_const_of_continuous_int hcont' hint
    exact ⟨k', fun x => by have := hk' x; linarith⟩
  obtain ⟨k', hk'⟩ := hk'ex
  have hcex : ∃ c : ℤ, ∀ x : ℝ, h' (h x) = x + (c : ℝ) := by
    have hcont : Continuous (fun x : ℝ => h' (h x) - x) := (h'hc.comp hhc).sub continuous_id
    have hint : ∀ x : ℝ, ∃ c : ℤ, h' (h x) - x = (c : ℝ) := by
      intro x
      have he : β (h' (h x)) = β x := by rw [← h'he (h x), hhe x]
      obtain ⟨j, hj⟩ := hβmod (h' (h x)) x he
      exact ⟨j, by rw [hj]; ring⟩
    obtain ⟨c, hc⟩ := lvcrep_exists_int_const_of_continuous_int hcont hint
    exact ⟨c, fun x => by have := hc x; linarith⟩
  obtain ⟨c, hc⟩ := hcex
  have hkk : (k : ℝ) * (k' : ℝ) = 1 := by
    have h1 : h' (h (0 + 1)) = h' (h 0) + (k : ℝ) * (k' : ℝ) := by
      rw [hk 0, lvcrep_shift_int_apply (h := h') (k := (k':ℝ)) hk' k (h 0)]
    rw [hc (0 + 1), hc 0] at h1
    linarith
  have hkk_int : k * k' = 1 := by exact_mod_cast hkk
  exact ⟨h, k, hhc, Int.eq_one_or_neg_one_of_mul_eq_one hkk_int, hk, hhe⟩

/-- **The direction of the reparametrisation.**  A continuous `h` with integer shift `k = ±1` and
`h x = h y → ∃ j : ℤ, x = y + j` is strictly monotone, with the sign of `k`. -/
theorem lvcrep_strictMono_or_strictAnti_of_lift {h : ℝ → ℝ} {k : ℤ}
    (hcont : Continuous h) (hk : ∀ x : ℝ, h (x + 1) = h x + (k : ℝ))
    (hk_pm : k = 1 ∨ k = -1)
    (hmod : ∀ x y : ℝ, h x = h y → ∃ j : ℤ, x = y + j) :
    (k = 1 ∧ StrictMono h) ∨ (k = -1 ∧ StrictAnti h) := by
  have hk_ne : (k:ℝ) ≠ 0 := by
    rcases hk_pm with h1 | h1
    · rw [h1]; norm_num
    · rw [h1]; norm_num
  have hinjIcc : ∀ x : ℝ, Set.InjOn h (Set.Icc x (x + 1)) := by
    intro x u hu v hv huv
    obtain ⟨j, hj⟩ := hmod u v huv
    have hux : x ≤ u := hu.1
    have hu1 : u ≤ x + 1 := hu.2
    have hvx : x ≤ v := hv.1
    have hv1 : v ≤ x + 1 := hv.2
    have hj_le : (j:ℝ) ≤ 1 := by linarith
    have hj_ge : (-1:ℝ) ≤ (j:ℝ) := by linarith
    have hj1 : j ≤ 1 := by exact_mod_cast hj_le
    have hj2 : -1 ≤ j := by exact_mod_cast hj_ge
    have hj_cases : j = -1 ∨ j = 0 ∨ j = 1 := by omega
    rcases hj_cases with h | h | h
    · have hv_eq : v = x + 1 := by rw [h] at hj; push_cast at hj; linarith
      have hu_eq : u = x := by rw [h] at hj; push_cast at hj; linarith
      rw [hv_eq, hu_eq, hk x] at huv
      exact absurd (by linarith : (k:ℝ) = 0) hk_ne
    · rw [h] at hj; push_cast at hj; linarith
    · have hu_eq : u = x + 1 := by rw [h] at hj; push_cast at hj; linarith
      have hv_eq : v = x := by rw [h] at hj; push_cast at hj; linarith
      rw [hu_eq, hv_eq, hk x] at huv
      exact absurd (by linarith : (k:ℝ) = 0) hk_ne
  rcases hk_pm with hk1 | hk1
  · left
    have hstep : ∀ x : ℝ, StrictMonoOn h (Set.Icc x (x + 1)) := by
      intro x
      refine ContinuousOn.strictMonoOn_of_injOn_Icc (by linarith) ?_ hcont.continuousOn
        (hinjIcc x)
      rw [hk x, hk1]; norm_num
    refine ⟨hk1, ?_⟩
    intro x y hxy
    set d : ℝ := y - x with hd
    have hdpos : 0 < d := by rw [hd]; linarith
    set m : ℤ := ⌊d⌋ with hm
    have hmle : (m:ℝ) ≤ d := Int.floor_le d
    have hmlt : d < (m:ℝ) + 1 := Int.lt_floor_add_one d
    have hm0 : 0 ≤ m := (Int.floor_nonneg (a := d)).mpr (le_of_lt hdpos)
    have hxt_le : x ≤ x + (d - (m:ℝ)) := by linarith
    have hxt_lt : x + (d - (m:ℝ)) ≤ x + 1 := by linarith
    have hy : y = (x + (d - (m:ℝ))) + (m:ℝ) := by rw [hd]; ring
    have hkey : h y = h (x + (d - (m:ℝ))) + (m:ℝ) := by
      have := lvcrep_shift_int_apply (h := h) (k := (k:ℝ)) hk m (x + (d - (m:ℝ)))
      rw [hy, this, hk1]
      push_cast
      ring
    have hmono : MonotoneOn h (Set.Icc x (x + 1)) := (hstep x).monotoneOn
    have hux : x ∈ Set.Icc x (x + 1) := ⟨le_refl x, by linarith⟩
    have hwx : (x + (d - (m:ℝ))) ∈ Set.Icc x (x + 1) := ⟨hxt_le, hxt_lt⟩
    rcases lt_or_eq_of_le hm0 with hmpos | hmeq
    · have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ m by omega)
      have hle : h x ≤ h (x + (d - (m:ℝ))) := hmono hux hwx hxt_le
      linarith
    · have hmz : (m:ℝ) = 0 := by rw [← hmeq]; norm_num
      have hstrict : h x < h (x + (d - (m:ℝ))) := (hstep x) hux hwx (by linarith)
      linarith
  · right
    have hstep : ∀ x : ℝ, StrictAntiOn h (Set.Icc x (x + 1)) := by
      intro x
      refine ContinuousOn.strictAntiOn_of_injOn_Icc (by linarith) ?_ hcont.continuousOn
        (hinjIcc x)
      rw [hk x, hk1]; norm_num
    refine ⟨hk1, ?_⟩
    intro x y hxy
    set d : ℝ := y - x with hd
    have hdpos : 0 < d := by rw [hd]; linarith
    set m : ℤ := ⌊d⌋ with hm
    have hmle : (m:ℝ) ≤ d := Int.floor_le d
    have hmlt : d < (m:ℝ) + 1 := Int.lt_floor_add_one d
    have hm0 : 0 ≤ m := (Int.floor_nonneg (a := d)).mpr (le_of_lt hdpos)
    have hxt_le : x ≤ x + (d - (m:ℝ)) := by linarith
    have hxt_lt : x + (d - (m:ℝ)) ≤ x + 1 := by linarith
    have hy : y = (x + (d - (m:ℝ))) + (m:ℝ) := by rw [hd]; ring
    have hkey : h y = h (x + (d - (m:ℝ))) - (m:ℝ) := by
      have := lvcrep_shift_int_apply (h := h) (k := (k:ℝ)) hk m (x + (d - (m:ℝ)))
      rw [hy, this, hk1]
      push_cast
      ring
    have hanti : AntitoneOn h (Set.Icc x (x + 1)) := (hstep x).antitoneOn
    have hux : x ∈ Set.Icc x (x + 1) := ⟨le_refl x, by linarith⟩
    have hwx : (x + (d - (m:ℝ))) ∈ Set.Icc x (x + 1) := ⟨hxt_le, hxt_lt⟩
    rcases lt_or_eq_of_le hm0 with hmpos | hmeq
    · have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ m by omega)
      have hle : h (x + (d - (m:ℝ))) ≤ h x := hanti hux hwx hxt_le
      linarith
    · have hmz : (m:ℝ) = 0 := by rw [← hmeq]; norm_num
      have hstrict : h (x + (d - (m:ℝ))) < h x := (hstep x) hux hwx (by linarith)
      linarith

/-- The coordinate projection of the model surface, in the `ofLp` form. -/
theorem lvcrep_proj_apply (i : Fin 2) (v : EuclideanSpace ℝ (Fin 2)) :
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i) v = v.ofLp i := rfl

/-- A nonzero vector of the model surface has a nonzero coordinate. -/
theorem lvcrep_exists_coord_of_ne_zero {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    ∃ i : Fin 2, x.ofLp i ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hx (by ext i; simpa using hc i)

/-- The manifold derivative of a real function, applied to `1`, is its derivative. -/
theorem lvcrep_mfderiv_one_apply (f : ℝ → ℝ) (x : ℝ) :
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) f x) ((1:ℝ) : TangentSpace 𝓘(ℝ,ℝ) x) = deriv f x := by
  rw [mfderiv_eq_fderiv]
  exact fderiv_eq_smul_deriv (f := f) (x := x) (1:ℝ) |>.trans (one_smul ℝ (deriv f x))

set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of a reparametrisation of a smooth immersion.**  If `α` and `β` are smooth
immersions into a surface and `h` is continuous with `β = α ∘ h`, then `h` is smooth and `deriv h`
never vanishes.  At a point `x₀`, in the chart at `β x₀`, the map `h` is the composite of the local
inverse of a coordinate of `α` with the same coordinate of `β`; the derivative statement follows by
differentiating `β = α ∘ h` and using that both derivatives are nonzero. -/
theorem lvcrep_contDiff_of_isReparam {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {α β : ℝ → M}
    (hαsm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) α)
    (hβsm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hαimm : ∀ x : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) α x ≠ 0)
    (hβimm : ∀ x : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) β x ≠ 0)
    {h : ℝ → ℝ} (hcont : Continuous h) (heq : ∀ x : ℝ, β x = α (h x)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ ∀ x : ℝ, deriv h x ≠ 0 := by
  have hcd : ∀ x₀ : ℝ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h x₀ := by
    intro x₀
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, (((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α (h x₀)) 1).ofLp i) ≠ 0 := by
      have hne : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α (h x₀)) 1 ≠ 0 := by
        intro h0
        refine hαimm (h x₀) (ContinuousLinearMap.ext_ring
          (f := mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α (h x₀)) (g := 0) ?_)
        rw [zero_apply]
        exact h0
      exact lvcrep_exists_coord_of_ne_zero hne
    set Θ : ℝ → ℝ := fun t => (extChartAt (𝓡 2) (β x₀) (α t)).ofLp i with hΘdef
    have hchart_deriv : mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (extChartAt (𝓡 2) (β x₀)) (α (h x₀))
        = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) (α (h x₀))) := by
      rw [← heq x₀]
      exact mfderiv_extChartAt_self
    have hΘcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ (h x₀) := by
      have hC : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (extChartAt (𝓡 2) (β x₀)) (α (h x₀)) := by
        rw [← heq x₀]
        exact contMDiffAt_extChartAt (I := 𝓡 2) (x := β x₀)
      have hcomp := hC.comp (h x₀) (hαsm.contMDiffAt)
      have hproj := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).contMDiffAt.comp (h x₀) hcomp
      have hfun : Θ = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i) ∘
          (extChartAt (𝓡 2) (β x₀) ∘ α) := by rw [hΘdef]; rfl
      rw [hfun]
      exact hproj.contDiffAt
    have hΘd : HasDerivAt Θ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i)
        ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α (h x₀)) 1)) (h x₀) := by
      have hmdα : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) α (h x₀) := hαsm.mdifferentiableAt (by simp)
      have hmdC : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (extChartAt (𝓡 2) (β x₀)) (α (h x₀)) := by
        rw [← heq x₀]
        exact mdifferentiableAt_extChartAt (I := 𝓡 2) (mem_chart_source _ _)
      have hfderiv := (hmdC.hasMFDerivAt.comp (h x₀) hmdα.hasMFDerivAt).hasFDerivAt
      have h1 := ((ContinuousLinearMap.hasFDerivAt
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i)).comp (h x₀) hfderiv).hasDerivAt
      rw [hchart_deriv] at h1
      simp only [ContinuousLinearMap.comp_apply] at h1
      have hfun : Θ = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i) ∘
          (extChartAt (𝓡 2) (β x₀) ∘ α) := by rw [hΘdef]; rfl
      rw [hfun]
      exact h1
    have hΘne : deriv Θ (h x₀) ≠ 0 := by
      rw [hΘd.deriv, lvcrep_proj_apply]
      exact hi
    have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv Θ (h x₀)) hΘne)
    have hsta : HasStrictFDerivAt Θ (e : ℝ →L[ℝ] ℝ) (h x₀) :=
      (hΘcd.hasStrictDerivAt hn).hasStrictFDerivAt_equiv hΘne
    have hfa : HasFDerivAt Θ (e : ℝ →L[ℝ] ℝ) (h x₀) := hsta.hasFDerivAt
    let g : ℝ → ℝ := hsta.localInverse Θ e (h x₀)
    have hsta_eq : hsta = hΘcd.hasStrictFDerivAt' hfa hn := Subsingleton.elim _ _
    have hge : g = hΘcd.localInverse hfa hn := by
      show hsta.localInverse Θ e (h x₀) = _
      rw [hsta_eq]
      rfl
    have hloc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hΘcd.localInverse hfa hn) (Θ (h x₀)) :=
      hΘcd.to_localInverse hfa hn
    have hgcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Θ (h x₀)) := by
      rw [hge]; exact hloc
    have hgleft : ∀ᶠ t in 𝓝 (h x₀), g (Θ t) = t := hsta.eventually_left_inverse
    have hβcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℝ => (extChartAt (𝓡 2) (β x₀) (β z)).ofLp i) x₀ := by
      have hC : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (extChartAt (𝓡 2) (β x₀)) (β x₀) := contMDiffAt_extChartAt (I := 𝓡 2) (x := β x₀)
      have hcomp := hC.comp x₀ (hβsm.contMDiffAt)
      have hproj := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).contMDiffAt.comp x₀ hcomp
      have hfun : (fun z : ℝ => (extChartAt (𝓡 2) (β x₀) (β z)).ofLp i) =
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i) ∘
            (extChartAt (𝓡 2) (β x₀) ∘ β) := rfl
      rw [hfun]
      exact hproj.contDiffAt
    have hpt : Θ (h x₀) = (extChartAt (𝓡 2) (β x₀) (β x₀)).ofLp i := by
      show (extChartAt (𝓡 2) (β x₀) (α (h x₀))).ofLp i = _
      rw [← heq x₀]
    have hgcd' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g
        ((extChartAt (𝓡 2) (β x₀) (β x₀)).ofLp i) := by
      rw [← hpt]; exact hgcd
    have hcomp2 := hgcd'.comp x₀ hβcd
    have hev : (fun z : ℝ => g ((extChartAt (𝓡 2) (β x₀) (β z)).ofLp i)) =ᶠ[𝓝 x₀] h := by
      have h1 : ∀ᶠ z in 𝓝 x₀, g (Θ (h z)) = h z := (hcont.tendsto x₀).eventually hgleft
      filter_upwards [h1] with z hz
      rw [← hz]
      congr 1
      show (extChartAt (𝓡 2) (β x₀) (β z)).ofLp i = Θ (h z)
      rw [hΘdef]
      rw [heq z]
    exact hcomp2.congr_of_eventuallyEq
      (show h =ᶠ[𝓝 x₀] (g ∘ fun z : ℝ => (extChartAt (𝓡 2) (β x₀) (β z)).ofLp i)
        from hev.symm)
  refine ⟨contDiff_iff_contDiffAt.mpr hcd, ?_⟩
  intro x hdx
  have hchain : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) β x) ((1:ℝ) : TangentSpace 𝓘(ℝ,ℝ) x) =
      (deriv h x) • ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α (h x))
        ((1:ℝ) : TangentSpace 𝓘(ℝ,ℝ) (h x))) := by
    have hmdα : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) α (h x) := hαsm.mdifferentiableAt (by simp)
    have hmdh : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) h x := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact (hcd x).differentiableAt (by simp)
    have hcomp := mfderiv_comp_apply (x := x) (g := α) (f := h) hmdα hmdh
      ((1:ℝ) : TangentSpace 𝓘(ℝ,ℝ) x)
    rw [show β = α ∘ h from funext heq, hcomp, lvcrep_mfderiv_one_apply]
    conv_lhs => rw [show (deriv h x : TangentSpace 𝓘(ℝ,ℝ) (h x)) =
      (deriv h x) • ((1:ℝ) : TangentSpace 𝓘(ℝ,ℝ) (h x)) by rw [smul_eq_mul, mul_one]]
    rw [ContinuousLinearMap.map_smul]
  have hzero : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) β x) ((1:ℝ) : TangentSpace 𝓘(ℝ,ℝ) x) = 0 := by
    rw [hchain, hdx, zero_smul]
  refine hβimm x (ContinuousLinearMap.ext_ring ?_)
  rw [zero_apply]
  exact hzero

/-- **The reparametrisation of a single component**: two `1`-periodic curves with the same range,
injective modulo `ℤ` and immersive, are related by a smooth `1`-periodic-up-to-`±1`
reparametrisation with nowhere-vanishing derivative of the matching sign. -/
theorem lvcrep_curveReparam_of_range_eq {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {α β : ℝ → M}
    (hαsm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) α)
    (hβsm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hαper : ∀ x : ℝ, α (x + 1) = α x) (hβper : ∀ x : ℝ, β (x + 1) = β x)
    (hαmod : ∀ x y : ℝ, α x = α y → ∃ k : ℤ, x = y + k)
    (hβmod : ∀ x y : ℝ, β x = β y → ∃ k : ℤ, x = y + k)
    (hαimm : ∀ x : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) α x ≠ 0)
    (hβimm : ∀ x : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) β x ≠ 0)
    (hrange : Set.range β = Set.range α) :
    ∃ (ε : ℤ) (h : ℝ → ℝ), (ε = 1 ∨ ε = -1) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      (∀ x : ℝ, h (x + 1) = h x + (ε : ℝ)) ∧
      (∀ x : ℝ, 0 < (ε : ℝ) * deriv h x) ∧
      (∀ x : ℝ, β x = α (h x)) := by
  obtain ⟨h, k, hhc, hk_pm, hk, hhe⟩ :=
    lvcrep_exists_lift_shift_pm_one hαsm.continuous hβsm.continuous hαper hβper hαmod hβmod
      hrange
  have hmod : ∀ x y : ℝ, h x = h y → ∃ j : ℤ, x = y + j := by
    intro x y hxy
    exact hβmod x y (by rw [hhe x, hhe y, hxy])
  obtain ⟨hcd, hderiv⟩ := lvcrep_contDiff_of_isReparam hαsm hβsm hαimm hβimm hhc hhe
  rcases lvcrep_strictMono_or_strictAnti_of_lift hhc hk hk_pm hmod with
    ⟨hk1, hmono⟩ | ⟨hk1, hanti⟩
  · refine ⟨k, h, hk_pm, hcd, hk, ?_, hhe⟩
    intro x
    have h1 : 0 ≤ deriv h x := hmono.monotone.deriv_nonneg
    have h2 : deriv h x ≠ 0 := hderiv x
    have h3 : 0 < deriv h x := lt_of_le_of_ne h1 (Ne.symm h2)
    rw [hk1]; push_cast
    exact mul_pos one_pos h3
  · refine ⟨k, h, hk_pm, hcd, hk, ?_, hhe⟩
    intro x
    have h1 : deriv h x ≤ 0 := hanti.antitone.deriv_nonpos
    have h2 : deriv h x ≠ 0 := hderiv x
    have h3 : deriv h x < 0 := lt_of_le_of_ne h1 h2
    rw [hk1]; push_cast
    nlinarith

theorem levelCurves_exists_transition {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {b : ℝ}
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    {n n' : ℕ} (L : Work.Drive.N2C.LevelCurves f b n) (L' : Work.Drive.N2C.LevelCurves f b n') :
    ∃ (σ : Fin n' → Fin n) (ε : Fin n' → ℤ) (h : Fin n' → ℝ → ℝ),
      Function.Bijective σ ∧ (∀ i : Fin n', ε i = 1 ∨ ε i = -1) ∧
      (∀ i : Fin n', ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h i)) ∧
      (∀ i : Fin n', ∀ x : ℝ, h i (x + 1) = h i x + (ε i : ℝ)) ∧
      (∀ i : Fin n', ∀ x : ℝ, 0 < (ε i : ℝ) * deriv (h i) x) ∧
      (∀ i : Fin n', ∀ x : ℝ, L'.γ i x = L.γ (σ i) (h i x)) := by
  obtain ⟨σ, hσbij, hrange⟩ := levelCurves_componentMatch L L'
  have hstep : ∀ i : Fin n', ∃ (ε : ℤ) (h : ℝ → ℝ), (ε = 1 ∨ ε = -1) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      (∀ x : ℝ, h (x + 1) = h x + (ε : ℝ)) ∧
      (∀ x : ℝ, 0 < (ε : ℝ) * deriv h x) ∧
      (∀ x : ℝ, L'.γ i x = L.γ (σ i) (h x)) := by
    intro i
    exact lvcrep_curveReparam_of_range_eq (L.sm (σ i)) (L'.sm i) (L.per (σ i)) (L'.per i)
      (L.modOne (σ i)) (L'.modOne i) (lvcrep_mfderiv_ne_zero L (σ i))
      (lvcrep_mfderiv_ne_zero L' i) (hrange i)
  choose ε h hε hsm hper hderiv heq using hstep
  exact ⟨σ, ε, h, hσbij, hε, hsm, hper, hderiv, heq⟩

end Work.Drive.N2C

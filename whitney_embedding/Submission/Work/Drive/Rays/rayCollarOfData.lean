import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.exists_collar_of_local_slabs
import Submission.Work.Noncompact.CompressionTube.exists_shrunk_tube
import Submission.Work.Drive.Rays.rayLocalSlabs

namespace Work.Drive.Rays

open scoped Manifold ContDiff
open Work.Noncompact.CompressionTube

noncomputable section

/-- The model with corners of `ℝ^{n-1} × ℝ` is the self model with corners. -/
theorem MCprod_eq_selfRay (n : ℕ) :
    MCprod n = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
  (modelWithCornersSelf_prod (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n - 1)))
    (F := ℝ)).symm

/-- `tubeSquash` is the radial compression `compress` of the shrunk-tube file. -/
theorem tubeSquash_eq_compress (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    tubeSquash n u = compress n u := rfl

/-- A smooth shrinking self-map of the parameter space of a tube: it is the radial compression
`(u,t) ↦ ((ρ t / 2) • (√(1+‖u‖²))⁻¹ • u, t)` on the half-space `0 ≤ p.2` and it clamps both
coordinates into the box `‖·‖ < c`, `|·| < c` on `p.2 < 0`. -/
theorem exists_rayHalfShrink (n : ℕ) {ρ : ℝ → ℝ}
    (hρcd : ContDiff ℝ smoothOrder ρ) (hρpos : ∀ t : ℝ, 0 < ρ t)
    {c : ℝ} (hc : 0 < c) (hρc : ∀ t : ℝ, t < 0 → ρ t ≤ c) :
    ∃ S : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
      ContMDiff (MCprod n) (MCprod n) smoothOrder S ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, 0 ≤ p.2 →
        S p = ((ρ p.2 / 2) • (Real.sqrt (1 + ‖p.1‖ ^ 2))⁻¹ • p.1, p.2)) ∧
      S ((0 : EuclideanSpace ℝ (Fin (n - 1))), 0) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), 0) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, 0 ≤ p.2 → ‖(S p).1‖ < ρ p.2) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, p.2 < 0 → ‖(S p).1‖ < c ∧ |(S p).2| < c) ∧
      Set.InjOn S {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ ≤ 1 ∧ 0 ≤ p.2} ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, 0 ≤ p.2 →
        Function.Injective (mfderiv (MCprod n) (MCprod n) S p)) := by
  classical
  set χ : ℝ → ℝ := fun t => Real.smoothTransition (2 * t / c + 2) with hχ
  have hχcd : ContDiff ℝ smoothOrder χ := by
    rw [hχ]
    exact Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const c).add contDiff_const)
  have hχ1 : ∀ t : ℝ, -c / 2 ≤ t → χ t = 1 := by
    intro t ht
    rw [hχ]
    refine Real.smoothTransition.one_of_one_le ?_
    have h : -1 ≤ 2 * t / c := by
      rw [le_div_iff₀ hc]
      linarith
    linarith
  have hχ0 : ∀ t : ℝ, t ≤ -c → χ t = 0 := by
    intro t ht
    rw [hχ]
    refine Real.smoothTransition.zero_of_nonpos ?_
    have h : 2 * t / c ≤ -2 := by
      rw [div_le_iff₀ hc]
      linarith
    linarith
  have hχnn : ∀ t : ℝ, 0 ≤ χ t := fun t => Real.smoothTransition.nonneg _
  have hχle : ∀ t : ℝ, χ t ≤ 1 := fun t => Real.smoothTransition.le_one _
  set A : ℝ → ℝ := fun t => χ t * (ρ t / 2) + (1 - χ t) * (c / 4) with hA
  set B : ℝ → ℝ := fun t => χ t * t + (1 - χ t) * (-3 * c / 4) with hB
  have hAcd : ContDiff ℝ smoothOrder A := by
    rw [hA]
    exact (hχcd.mul (hρcd.div_const 2)).add ((contDiff_const.sub hχcd).mul contDiff_const)
  have hBcd : ContDiff ℝ smoothOrder B := by
    rw [hB]
    exact (hχcd.mul contDiff_id).add ((contDiff_const.sub hχcd).mul contDiff_const)
  have hA1 : ∀ t : ℝ, -c / 2 ≤ t → A t = ρ t / 2 := by
    intro t ht
    have hχt : χ t = 1 := hχ1 t ht
    simp only [hA, hχt, one_mul, sub_self, zero_mul, add_zero]
  have hB1 : ∀ t : ℝ, -c / 2 ≤ t → B t = t := by
    intro t ht
    have hχt : χ t = 1 := hχ1 t ht
    simp only [hB, hχt, one_mul, sub_self, zero_mul, add_zero]
  have hApos : ∀ t : ℝ, 0 < A t := by
    intro t
    have h3 : 0 < ρ t / 2 := by linarith [hρpos t]
    have h4 : 0 < c / 4 := by linarith
    rcases lt_or_eq_of_le (hχnn t) with hlt | heq
    · have h1 : 0 < χ t * (ρ t / 2) := mul_pos hlt h3
      have h2 : 0 ≤ (1 - χ t) * (c / 4) :=
        mul_nonneg (by linarith [hχle t]) (le_of_lt h4)
      simp only [hA]
      linarith
    · have hχt : χ t = 0 := heq.symm
      simp only [hA, hχt, zero_mul, sub_zero, one_mul]
      linarith
  have hAle : ∀ t : ℝ, t < 0 → A t ≤ c / 2 := by
    intro t ht
    have h4 : ρ t ≤ c := hρc t ht
    have h1 : 0 ≤ χ t := hχnn t
    have h2 : χ t ≤ 1 := hχle t
    simp only [hA]
    nlinarith
  set S : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
    fun p => (A p.2 • tubeSquash n p.1, B p.2) with hS
  have hScd : ContDiff ℝ smoothOrder S := by
    rw [hS]
    have h3 : ContDiff ℝ smoothOrder
        (fun p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => A p.2 • tubeSquash n p.1) :=
      (hAcd.comp contDiff_snd).smul ((tubeSquash_contDiff n).comp contDiff_fst)
    have h4 : ContDiff ℝ smoothOrder
        (fun p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => B p.2) := hBcd.comp contDiff_snd
    exact h3.prodMk h4
  have hScont : ContMDiff (MCprod n) (MCprod n) smoothOrder S := by
    rw [MCprod_eq_selfRay]
    exact (contMDiff_iff_contDiff).2 hScd
  refine ⟨S, hScont, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hp' : -c / 2 ≤ p.2 := by linarith
    simp only [hS, hA1 p.2 hp', hB1 p.2 hp', tubeSquash]
  · have h0 : -c / 2 ≤ (0 : ℝ) := by linarith
    simp only [hS, tubeSquash_zero, hB1 0 h0]
    simp
  · intro p hp
    have hp' : -c / 2 ≤ p.2 := by linarith
    have hρ2 : 0 < ρ p.2 / 2 := by linarith [hρpos p.2]
    simp only [hS, hA1 p.2 hp']
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt hρ2)]
    have h3 : ‖tubeSquash n p.1‖ < 1 := tubeSquash_norm_lt_one n p.1
    have h4 : 0 < ρ p.2 := hρpos p.2
    nlinarith
  · intro p hp
    constructor
    · have h4 : A p.2 ≤ c / 2 := hAle p.2 hp
      simp only [hS]
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt (hApos p.2))]
      have h3 : ‖tubeSquash n p.1‖ < 1 := tubeSquash_norm_lt_one n p.1
      have h5 : 0 < A p.2 := hApos p.2
      nlinarith
    · simp only [hS]
      by_cases hle : p.2 ≤ -c
      · have h0 : χ p.2 = 0 := hχ0 p.2 hle
        simp only [hB, h0, zero_mul, sub_zero, one_mul]
        rw [abs_of_neg (by linarith)]
        linarith
      · have hlt : -c < p.2 := not_le.mp hle
        have h1 : 0 ≤ χ p.2 := hχnn p.2
        have h2 : χ p.2 ≤ 1 := hχle p.2
        have hb1 : -c < χ p.2 * p.2 + (1 - χ p.2) * (-3 * c / 4) := by nlinarith
        have hb2 : χ p.2 * p.2 + (1 - χ p.2) * (-3 * c / 4) < 0 := by nlinarith
        simp only [hB, abs_of_neg hb2]
        linarith
  · intro p hp q hq hpq
    have hsnd : B p.2 = B q.2 := by
      have h := congrArg Prod.snd hpq
      simpa only [hS] using h
    have hp2 : -c / 2 ≤ p.2 := by linarith [hp.2]
    have hq2 : -c / 2 ≤ q.2 := by linarith [hq.2]
    have heq2 : p.2 = q.2 := by
      rw [hB1 p.2 hp2, hB1 q.2 hq2] at hsnd
      exact hsnd
    have hfst : A p.2 • tubeSquash n p.1 = A q.2 • tubeSquash n q.1 := by
      have h := congrArg Prod.fst hpq
      simpa only [hS] using h
    rw [heq2, hA1 q.2 hq2] at hfst
    have hne : ρ q.2 / 2 ≠ 0 := by linarith [hρpos q.2]
    have h3 : tubeSquash n p.1 = tubeSquash n q.1 :=
      smul_right_injective (EuclideanSpace ℝ (Fin (n - 1))) hne hfst
    exact Prod.ext (tubeSquash_injective n h3) heq2
  · intro p hp
    have hp2 : -c / 2 < p.2 := by linarith
    have hev : S =ᶠ[nhds p] (shrink n (fun t : ℝ => ρ t / 2)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp2] with q hq
      have hq2 : -c / 2 ≤ q.2 := le_of_lt hq
      show (A q.2 • tubeSquash n q.1, B q.2) = ((fun t : ℝ => ρ t / 2) q.2 • compress n q.1, q.2)
      simp only [hA1 q.2 hq2, hB1 q.2 hq2, tubeSquash_eq_compress]
    rw [hev.mfderiv_eq]
    exact shrink_mfderiv_injective n (hρcd.div_const 2) (fun t => by linarith [hρpos t]) p

/-! ## The one-sided availability radius -/

/-- **Availability radius, one-sided version.**  Given positive functions `R`, `E` with `R s ≤ 1`
for `s ≥ 0`, and a constant `c > 0`, there is a smooth positive `ρ` with `ρ t ≤ c` for `t < 0`
such that every point `(v,t)` with `t ≥ 0` and `‖v‖ < ρ t` lies in the slab
`{‖v‖ < R s, |t - s| < E s}` of some index `s ≥ 0`. -/
theorem exists_radius_minorant_ray {m : ℕ} {R E : ℝ → ℝ}
    (hR : ∀ s : ℝ, 0 ≤ s → 0 < R s) (hE : ∀ s : ℝ, 0 < E s)
    (hR1 : ∀ s : ℝ, 0 ≤ s → R s ≤ 1) {c : ℝ} (hc : 0 < c) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ smoothOrder ρ ∧ (∀ t : ℝ, 0 < ρ t) ∧
      (∀ t : ℝ, t < 0 → ρ t ≤ c) ∧
      ∀ (v : EuclideanSpace ℝ (Fin m)) (t : ℝ), 0 ≤ t → ‖v‖ < ρ t →
        ∃ s : ℝ, 0 ≤ s ∧ |t - s| < E s ∧ ‖v‖ < R s := by
  classical
  set A : ℝ → ℝ := fun t => sSup {x : ℝ | ∃ s : ℝ, 0 ≤ s ∧ |t - s| < E s ∧ x = R s} with hA
  have hbdd : ∀ t : ℝ, BddAbove {x : ℝ | ∃ s : ℝ, 0 ≤ s ∧ |t - s| < E s ∧ x = R s} := by
    intro t
    refine ⟨1, ?_⟩
    rintro x ⟨s, hs, -, rfl⟩
    exact hR1 s hs
  have hmem : ∀ t : ℝ, 0 ≤ t → R t ∈ {x : ℝ | ∃ s : ℝ, 0 ≤ s ∧ |t - s| < E s ∧ x = R s} := by
    intro t ht
    exact ⟨t, ht, by simpa using hE t, rfl⟩
  have hApos : ∀ t : ℝ, 0 ≤ t → 0 < A t := by
    intro t ht
    have h1 : R t ≤ A t := by
      rw [hA]
      exact le_csSup (hbdd t) (hmem t ht)
    linarith [hR t ht]
  have hAlsc : ∀ t₀ : ℝ, 0 ≤ t₀ → LowerSemicontinuousAt A t₀ := by
    intro t₀ ht₀
    rw [lowerSemicontinuousAt_iff]
    intro a ha
    rw [hA] at ha
    obtain ⟨x, ⟨s, hs, hxs, hxs'⟩, hax⟩ := (lt_csSup_iff (hbdd t₀) ⟨R t₀, hmem t₀ ht₀⟩).mp ha
    rw [hxs'] at hax
    have hI : {t : ℝ | |t - s| < E s} ∈ nhds t₀ :=
      (isOpen_Iio.preimage ((continuous_id.sub continuous_const).abs)).mem_nhds hxs
    filter_upwards [hI] with t ht
    have h1 : R s ≤ A t := by
      rw [hA]
      exact le_csSup (hbdd t) ⟨s, hs, ht, rfl⟩
    linarith
  set B : ℝ → ℝ := fun t => if t < 0 then c else min c (A t) with hB
  have hBpos : ∀ t : ℝ, 0 < B t := by
    intro t
    simp only [hB]
    by_cases ht : t < 0
    · rw [if_pos ht]; exact hc
    · rw [if_neg ht]
      exact lt_min hc (hApos t (not_lt.mp ht))
  have hBlsc : LowerSemicontinuous B := by
    rw [lowerSemicontinuous_iff]
    intro t₀
    rw [lowerSemicontinuousAt_iff]
    intro a ha
    by_cases h0 : t₀ < 0
    · simp only [hB] at ha
      rw [if_pos h0] at ha
      filter_upwards [isOpen_Iio.mem_nhds h0] with t ht
      have ht' : t < 0 := ht
      have hBt : B t = c := by simp only [hB]; rw [if_pos ht']
      rw [hBt]
      exact ha
    · have ht₀ : 0 ≤ t₀ := not_lt.mp h0
      simp only [hB] at ha
      rw [if_neg h0] at ha
      have haA : a < A t₀ := lt_of_lt_of_le ha (min_le_right _ _)
      have hac : a < c := lt_of_lt_of_le ha (min_le_left _ _)
      filter_upwards [hAlsc t₀ ht₀ a haA] with t ht
      simp only [hB]
      by_cases ht' : t < 0
      · rw [if_pos ht']; exact hac
      · rw [if_neg ht']; exact lt_min hac ht
  obtain ⟨ρ, hρcd, hρpos, hρle⟩ := exists_smooth_minorant_lsc hBpos hBlsc
  refine ⟨ρ, hρcd, hρpos, ?_, ?_⟩
  · intro t ht
    have hBt : B t = c := by simp only [hB]; rw [if_pos ht]
    exact le_trans (hρle t) (le_of_eq hBt)
  · intro v t ht hv
    have h1 : ‖v‖ < B t := lt_of_lt_of_le hv (hρle t)
    have hBt : B t = min c (A t) := by simp only [hB]; rw [if_neg (not_lt.mpr ht)]
    rw [hBt] at h1
    have h2 : ‖v‖ < A t := lt_of_lt_of_le h1 (min_le_right _ _)
    rw [hA] at h2
    obtain ⟨x, ⟨s, hs, hxs, hxs'⟩, hvx⟩ := (lt_csSup_iff (hbdd t) ⟨R t, hmem t ht⟩).mp h2
    rw [hxs'] at hvx
    exact ⟨s, hs, hxs, hvx⟩

/-! ## The collar along a ray from one-sided local slabs -/

/-- **The one-sided collar from local slab data.** -/
theorem ray_collar_of_slabs {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} {r : ℝ → M}
    {g : M → ℝ} {P : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (hP : ContMDiff (MC n) (MC (n - 1)) smoothOrder P)
    {rad eps : ℝ → ℝ} {σ : ℝ → EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M}
    (hrad : ∀ s : ℝ, 0 ≤ s → 0 < rad s) (heps : ∀ s : ℝ, 0 < eps s)
    (hσsm : ∀ s : ℝ, 0 ≤ s → ContMDiffOn (MCprod n) (MC n) smoothOrder (σ s)
      {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ < rad s ∧ |p.2 - s| < eps s})
    (hσcore : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |t - s| < eps s →
      σ s ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = r t)
    (hσsect : ∀ (s : ℝ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ), 0 ≤ s →
      ‖p.1‖ < rad s → |p.2 - s| < eps s → (P (σ s p), g (σ s p)) = p)
    (hσW : ∀ (s : ℝ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ), 0 ≤ s →
      ‖p.1‖ < rad s → |p.2 - s| < eps s → σ s p ∈ W) :
    ∃ Ψ : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M,
      ContMDiff (MCprod n) (MC n) smoothOrder Ψ ∧
      Ψ ((0 : EuclideanSpace ℝ (Fin (n - 1))), 0) = r 0 ∧
      Set.InjOn Ψ {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ ≤ 1 ∧ 0 ≤ p.2} ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → 0 ≤ p.2 →
        Function.Injective (mfderiv (MCprod n) (MC n) Ψ p)) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → 0 ≤ p.2 → Ψ p ∈ W) ∧
      (∀ K : Set M, IsCompact K → ∃ S : ℝ, ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
        ‖p.1‖ ≤ 1 → S ≤ p.2 → Ψ p ∉ K) := by
  classical
  have hηsm : ContMDiff (MC n) (MCprod n) smoothOrder (fun x : M => (P x, g x)) := by
    rw [prodModel_eq_self (n := n)]
    exact (contMDiff_prod_module_iff (I := MC n) (f := fun x : M => (P x, g x))).2 ⟨hP, hg⟩
  set slab : ℝ → Set (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
    fun s => {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ < rad s ∧ |p.2 - s| < eps s}
    with hslab
  have hslabmem : ∀ (s : ℝ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ),
      (p ∈ slab s) ↔ (‖p.1‖ < rad s ∧ |p.2 - s| < eps s) := by
    intro s p; simp only [hslab, Set.mem_ofPred_eq]
  have hslabopen : ∀ s : ℝ, IsOpen (slab s) := by
    intro s
    simp only [hslab]
    exact (isOpen_lt continuous_fst.norm continuous_const).inter
      (isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const)
  have hσsm' : ∀ s : ℝ, 0 ≤ s → ContMDiffOn (MCprod n) (MC n) smoothOrder (σ s) (slab s) := by
    intro s hs
    simp only [hslab]
    exact hσsm s hs
  have hσsect' : ∀ (s : ℝ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ), 0 ≤ s →
      p ∈ slab s → (P (σ s p), g (σ s p)) = p := by
    intro s p hs hp
    obtain ⟨h1, h2⟩ := (hslabmem s p).mp hp
    exact hσsect s p hs h1 h2
  set U : Set (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
    ⋃ s : {s : ℝ // 0 ≤ s}, slab (s : ℝ) with hU
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_iUnion (fun s => hslabopen (s : ℝ))
  have hUunfold : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, p ∈ U →
      ∃ s : ℝ, 0 ≤ s ∧ p ∈ slab s := by
    intro p hp
    rw [hU] at hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact ⟨(i : ℝ), i.2, hi⟩
  have hmemU : ∀ (s : ℝ) (hs : 0 ≤ s) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ),
      p ∈ slab s → p ∈ U := by
    intro s hs p hp
    rw [hU]
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hp⟩
  set sIdx : (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) → ℝ :=
    fun p => if hp : p ∈ U then (Classical.choose (hUunfold p hp)) else 0
    with hsIdxdef
  have hsIdx_eq : ∀ (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (hp : p ∈ U),
      sIdx p = (Classical.choose (hUunfold p hp)) := by
    intro p hp
    change (if hp' : p ∈ U then (Classical.choose (hUunfold p hp')) else 0)
      = (Classical.choose (hUunfold p hp))
    rw [dif_pos hp]
  have hsIdx_mem : ∀ (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (hp : p ∈ U),
      p ∈ slab (sIdx p) := by
    intro p hp
    rw [hsIdx_eq p hp]
    exact (Classical.choose_spec (hUunfold p hp)).2
  have hsIdx_nonneg : ∀ (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (hp : p ∈ U),
      0 ≤ sIdx p := by
    intro p hp
    rw [hsIdx_eq p hp]
    exact (Classical.choose_spec (hUunfold p hp)).1
  have hagree : ∀ (s s' : ℝ), 0 ≤ s → 0 ≤ s' → (slab s ∩ slab s').Nonempty →
      ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, p ∈ slab s → p ∈ slab s' →
        σ s p = σ s' p := by
    intro s s' hs hs' hne p hp hp'
    obtain ⟨q, hq⟩ := hne
    have hq1 : |q.2 - s| < eps s := ((hslabmem s q).mp hq.1).2
    have hq2 : |q.2 - s'| < eps s' := ((hslabmem s' q).mp hq.2).2
    set t : ℝ := if 0 ≤ q.2 then q.2 else 0 with htdef
    have ht0 : 0 ≤ t := by
      by_cases h : 0 ≤ q.2
      · have htq : t = q.2 := by rw [htdef, if_pos h]
        exact htq ▸ h
      · have htq : t = 0 := by rw [htdef, if_neg h]
        exact htq ▸ le_rfl
    have hts : |t - s| < eps s := by
      by_cases h : 0 ≤ q.2
      · simpa only [htdef, if_pos h] using hq1
      · have h1 : s - eps s < q.2 := by linarith [(abs_lt.mp hq1).1]
        simp only [htdef, if_neg h, zero_sub, abs_neg, abs_of_nonneg hs]
        linarith [heps s]
    have hts' : |t - s'| < eps s' := by
      by_cases h : 0 ≤ q.2
      · simpa only [htdef, if_pos h] using hq2
      · have h1 : s' - eps s' < q.2 := by linarith [(abs_lt.mp hq2).1]
        simp only [htdef, if_neg h, zero_sub, abs_neg, abs_of_nonneg hs']
        linarith [heps s']
    have haxis1 : ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) ∈ slab s :=
      (hslabmem s _).mpr ⟨by simpa using hrad s hs, hts⟩
    have haxis2 : ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) ∈ slab s' :=
      (hslabmem s' _).mpr ⟨by simpa using hrad s' hs', hts'⟩
    have h0eq : σ s ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = σ s' ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) := by
      rw [hσcore s t hs ht0 hts, hσcore s' t hs' ht0 hts']
    have hconv : Convex ℝ (slab s ∩ slab s') := by
      simp only [hslab]
      exact convex_slab_inter
    exact sections_eqOn_of_convex (by omega : 1 ≤ n) hηsm (hslabopen s) (hslabopen s')
      (hσsm' s hs) (hσsm' s' hs') (fun r hr => hσsect' s r hs hr)
      (fun r hr => hσsect' s' r hs' hr) hconv ⟨haxis1, haxis2⟩ h0eq p ⟨hp, hp'⟩
  set Ψ₀ : (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) → M := fun p => σ (sIdx p) p with hΨ0def
  have hΨ0val : ∀ (s : ℝ) (hs : 0 ≤ s) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ),
      p ∈ slab s → Ψ₀ p = σ s p := by
    intro s hs p hp
    have h1 : Ψ₀ p = σ (sIdx p) p := by simp only [hΨ0def]
    rw [h1]
    exact hagree (sIdx p) s (hsIdx_nonneg p (hmemU s hs p hp)) hs
      ⟨p, hsIdx_mem p (hmemU s hs p hp), hp⟩ p (hsIdx_mem p (hmemU s hs p hp)) hp
  have hΨ0sm : ContMDiffOn (MCprod n) (MC n) smoothOrder Ψ₀ U := by
    intro p hp
    obtain ⟨i, hi1, hi2⟩ := hUunfold p hp
    have hcongr : ContMDiffOn (MCprod n) (MC n) smoothOrder Ψ₀ (U ∩ slab i) :=
      ((hσsm' i hi1).mono Set.inter_subset_right).congr
        (fun q hq => hΨ0val i hi1 q hq.2)
    exact (hcongr.contMDiffAt ((hUopen.inter (hslabopen i)).mem_nhds ⟨hp, hi2⟩)).contMDiffWithinAt
  have hΨ0sect : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, p ∈ U →
      (P (Ψ₀ p), g (Ψ₀ p)) = p := by
    intro p hp
    obtain ⟨i, hi1, hi2⟩ := hUunfold p hp
    rw [hΨ0val i hi1 p hi2]
    exact hσsect' i p hi1 hi2
  have hΨ0core : ∀ t : ℝ, 0 ≤ t → Ψ₀ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = r t := by
    intro t ht
    have hmem : ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) ∈ slab t :=
      (hslabmem t _).mpr ⟨by simpa using hrad t ht, by simpa using heps t⟩
    rw [hΨ0val t ht _ hmem]
    exact hσcore t t ht ht (by simpa using heps t)
  have hΨ0imm : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, p ∈ U →
      Function.Injective (mfderiv (MCprod n) (MC n) Ψ₀ p) := by
    intro p hp
    obtain ⟨i, hi1, hi2⟩ := hUunfold p hp
    have hev : Ψ₀ =ᶠ[nhds p] σ i :=
      Filter.eventuallyEq_of_mem ((hUopen.inter (hslabopen i)).mem_nhds ⟨hp, hi2⟩)
        (fun q hq => hΨ0val i hi1 q hq.2)
    rw [hev.mfderiv_eq]
    exact (injective_mfderiv_of_section hηsm (hslabopen i) (hσsm' i hi1)
      (fun q hq => hσsect' i q hi1 hq) hi2).1
  -- the small constant and the radius minorant
  set cc : ℝ := min (rad 0) (eps 0) / 4 with hccdef
  have hminpos : 0 < min (rad 0) (eps 0) := lt_min (hrad 0 le_rfl) (heps 0)
  have hccpos : 0 < cc := by simp only [hccdef]; linarith
  have hccrad : cc < rad 0 := by
    simp only [hccdef]; have := min_le_left (rad 0) (eps 0); linarith
  have hcceps : cc < eps 0 := by
    simp only [hccdef]; have := min_le_right (rad 0) (eps 0); linarith
  obtain ⟨ρ, hρcd, hρpos, hρneg, hρcov⟩ :=
    exists_radius_minorant_ray (m := n - 1) (R := fun s => min (rad s) 1) (E := eps)
      (fun s hs => lt_min (hrad s hs) one_pos) heps (fun s hs => min_le_right _ _) hccpos
  obtain ⟨S, hScd, hSform, hS00, hSnorm, hSclamp, hSinj, hSimm⟩ :=
    exists_rayHalfShrink (n := n) hρcd hρpos hccpos hρneg
  have hSmemU : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, S p ∈ U := by
    intro p
    by_cases hp : 0 ≤ p.2
    · have h1 : ‖(S p).1‖ < ρ p.2 := hSnorm p hp
      have h2 : (S p).2 = p.2 := by rw [hSform p hp]
      obtain ⟨s, hs, hse, hsr⟩ := hρcov (S p).1 p.2 hp h1
      refine hmemU s hs (S p) ((hslabmem s (S p)).mpr ⟨lt_of_lt_of_le hsr (min_le_left _ _), ?_⟩)
      rw [h2]
      exact hse
    · have hp' : p.2 < 0 := not_le.mp hp
      obtain ⟨h1, h2⟩ := hSclamp p hp'
      exact hmemU 0 le_rfl (S p)
        ((hslabmem 0 (S p)).mpr ⟨by linarith, by rw [sub_zero]; linarith⟩)
  refine ⟨fun p => Ψ₀ (S p), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (hΨ0sm (S p) (hSmemU p)).contMDiffAt (hUopen.mem_nhds (hSmemU p)) |>.comp p hScd.contMDiffAt
  · show Ψ₀ (S ((0 : EuclideanSpace ℝ (Fin (n - 1))), 0)) = r 0
    rw [hS00]
    exact hΨ0core 0 le_rfl
  · intro p hp q hq hpq
    have h2 : S p = S q := by
      have h3 : (P (Ψ₀ (S p)), g (Ψ₀ (S p))) = (P (Ψ₀ (S q)), g (Ψ₀ (S q))) := by
        have hpq' : Ψ₀ (S p) = Ψ₀ (S q) := hpq
        rw [hpq']
      rw [hΨ0sect (S p) (hSmemU p), hΨ0sect (S q) (hSmemU q)] at h3
      exact h3
    exact hSinj hp hq h2
  · intro p hp1 hp2
    have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
    have hmd1 : MDifferentiableAt (MCprod n) (MC n) Ψ₀ (S p) :=
      ((hΨ0sm (S p) (hSmemU p)).contMDiffAt (hUopen.mem_nhds (hSmemU p))).mdifferentiableAt hn0
    have hmd2 : MDifferentiableAt (MCprod n) (MCprod n) S p :=
      hScd.contMDiffAt.mdifferentiableAt hn0
    have hchain : mfderiv (MCprod n) (MC n) (fun p => Ψ₀ (S p)) p
        = (mfderiv (MCprod n) (MC n) Ψ₀ (S p)).comp (mfderiv (MCprod n) (MCprod n) S p) :=
      mfderiv_comp (I := MCprod n) (I' := MCprod n) (I'' := MC n) (f := S) (g := Ψ₀) p hmd1 hmd2
    rw [hchain]
    intro v w hvw
    exact hSimm p hp2 (hΨ0imm (S p) (hSmemU p) hvw)
  · intro p hp1 hp2
    have h1 : ‖(S p).1‖ < ρ p.2 := hSnorm p hp2
    have h2 : (S p).2 = p.2 := by rw [hSform p hp2]
    obtain ⟨s, hs, hse, hsr⟩ := hρcov (S p).1 p.2 hp2 h1
    have hmem1 : ‖(S p).1‖ < rad s := lt_of_lt_of_le hsr (min_le_left _ _)
    have hmem2 : |(S p).2 - s| < eps s := by rw [h2]; exact hse
    have hmem : S p ∈ slab s := (hslabmem s (S p)).mpr ⟨hmem1, hmem2⟩
    show Ψ₀ (S p) ∈ W
    rw [hΨ0val s hs (S p) hmem]
    exact hσW s (S p) hs hmem1 hmem2
  · intro K hK
    obtain ⟨C, hC⟩ := (hK.image hg.continuous).isBounded.exists_norm_le
    refine ⟨max C 0 + 1, ?_⟩
    intro p hp1 hp2 hmemK
    have hp2pos : 0 ≤ p.2 := by linarith [le_max_right C 0]
    have hmemK' : Ψ₀ (S p) ∈ K := hmemK
    have h1 : g (Ψ₀ (S p)) ∈ g '' K := ⟨Ψ₀ (S p), hmemK', rfl⟩
    have h2 : ‖g (Ψ₀ (S p))‖ ≤ C := hC _ h1
    have h3 : g (Ψ₀ (S p)) = p.2 := by
      have h4 : g (Ψ₀ (S p)) = (S p).2 := by
        have h5 := congrArg Prod.snd (hΨ0sect (S p) (hSmemU p))
        simpa using h5
      rw [h4, hSform p hp2pos]
    rw [h3, Real.norm_eq_abs, abs_of_nonneg hp2pos] at h2
    have hCmax : C ≤ max C 0 := le_max_left C 0
    linarith


open scoped Manifold ContDiff in
open Work.Noncompact.CompressionTube in
theorem rayCollarOfData {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) {r : ℝ → M}
    (hrsm : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    (hrinj : Set.InjOn r (Set.Ici (0:ℝ)))
    (hrp : IsProperMap (fun t : Set.Ici (0:ℝ) => r t))
    (hrimm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t))
    (hrW : ∀ t : ℝ, 0 ≤ t → r t ∈ W)
    {g : M → ℝ} {P : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (hP : ContMDiff (MC n) (MC (n - 1)) smoothOrder P)
    (hgcore : ∀ t : ℝ, 0 ≤ t → g (r t) = t)
    (hPcore : ∀ t : ℝ, 0 ≤ t → P (r t) = 0)
    (htrans : ∀ t : ℝ, 0 ≤ t → ∀ v : TangentSpace (MC n) (r t),
      mfderiv (MC n) (MC (n - 1)) P (r t) v = 0 →
      mfderiv (MC n) MCreal g (r t) v = 0 → v = 0) :
    ∃ Ψ : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M,
      ContMDiff (MCprod n) (MC n) smoothOrder Ψ ∧
      Ψ ((0 : EuclideanSpace ℝ (Fin (n - 1))), 0) = r 0 ∧
      Set.InjOn Ψ {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ ≤ 1 ∧ 0 ≤ p.2} ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → 0 ≤ p.2 →
        Function.Injective (mfderiv (MCprod n) (MC n) Ψ p)) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → 0 ≤ p.2 → Ψ p ∈ W) ∧
      (∀ K : Set M, IsCompact K → ∃ S : ℝ, ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
        ‖p.1‖ ≤ 1 → S ≤ p.2 → Ψ p ∉ K) := by
  obtain ⟨rad, eps, σ, hrad, heps, hσsm, hσcore, hσsect, hσW⟩ :=
    rayLocalSlabs (n := n) hn hW hrsm hg hP hgcore hPcore hrW htrans
  exact ray_collar_of_slabs (n := n) hn hg hP hrad heps hσsm hσcore hσsect hσW

end

end Work.Drive.Rays

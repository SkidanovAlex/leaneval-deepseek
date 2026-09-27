import Mathlib
import Submission.Work.ManifoldParity.Defs

/-!
# The regular zero set of a `C^∞` function on the plane is locally a graph (the C^∞ twin)

This is the `C^∞` twin of `Submission/Work/Drive/hasLocalGraphCharts_regular_zeroSet.lean` (which is
stated at order `1` and feeds the `C¹` level-set arc chapter `GM1`/`ODC1`).  Its output is in the
*C^∞* graph-chart vocabulary `Work.ManifoldParity.HasLocalGraphCharts`
(`Submission/Work/ManifoldParity/Defs.lean`), which the C^∞ chapter
`Work.ManifoldParity.exists_circle_parametrization` and the C^∞ one-manifold classification
`Work.OneDim.classify_connected_one_manifold` consume.  It is the first piece of the `C^∞` version of
the level-set arc chapter — the obstruction located in `CUT_CHORD_STATUS.md` §2 item 3.

Let `h : ℝ² → ℝ` be `C^∞` and let `z` be a zero of `h` with `fderiv ℝ h z ≠ 0`.  Then, near `z`,
the zero set `{h = 0}` is the graph of a `C^∞` function over one of the two coordinate axes.

The proof is the implicit function theorem in coordinates: since `fderiv ℝ h z ≠ 0`, some
partial derivative `∂ᵢ h (z)` does not vanish, and the map
`(x, t) ↦ (t, h (x + t • eᵢ))`  (`x` ranging over the whole plane) is a local homeomorphism near
`(z - zᵢ • eᵢ, zᵢ)` whose inverse is `C¹` on a neighbourhood of `(0, z - zᵢ • eᵢ)`; its second
component, read off the slice `t = 0`, is the graph function.  A `C¹` bump function then makes the
graph function globally `C¹` without changing it near `z`.

The main theorem of this file,
`Work.Drive.hasLocalGraphCharts_regular_zeroSet`, deduces
`Work.ManifoldParity.HasLocalGraphCharts` for a truncated regular zero set
`{h = 0} ∩ {‖z‖ < R}`.
-/

namespace Work.Drive.SmoothGraph

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-- `EuclideanSpace ℝ (Fin 2)`, the model space of the plane in this file. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The `i`-th standard basis vector of `E2`. -/
abbrev e2 (i : Fin 2) : E2 := EuclideanSpace.single i (1 : ℝ)

/-! ### Elementary facts about the two coordinate directions -/

/-- Decomposition of a plane vector along the two coordinate directions. -/
theorem e2_decomp {i j : Fin 2} (hij : i ≠ j) (y : E2) :
    y = (y j) • e2 j + (y i) • e2 i := by
  ext k
  fin_cases i <;> fin_cases j <;> simp_all <;> (fin_cases k <;> simp_all)

/-- The `j`-th coordinate of a multiple of `eᵢ` vanishes when `i ≠ j`. -/
theorem e2_smul_apply_ne {i j : Fin 2} (hij : i ≠ j) (c : ℝ) : (c • e2 i) j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- The `j`-th coordinate of a multiple of `eⱼ` is the scalar. -/
theorem e2_smul_apply_self (j : Fin 2) (c : ℝ) : (c • e2 j) j = c := by
  simp [e2, PiLp.smul_apply]

/-- Subtracting the `i`-th coordinate of `p` times `eᵢ` from `p` leaves the projection onto the
other coordinate direction. -/
theorem sub_smul_eq {i j : Fin 2} (hij : i ≠ j) (p : E2) :
    p - (p i) • e2 i = (p j) • e2 j := by
  rw [sub_eq_iff_eq_add]
  exact e2_decomp hij p

/-- `e₂ j` is a unit vector. -/
theorem norm_smul_e2 (j : Fin 2) (t : ℝ) : ‖t • e2 j‖ = |t| := by
  rw [norm_smul, Real.norm_eq_abs, e2, PiLp.norm_single]
  simp

/-! ### Two linear-algebra lemmas -/

/-- A continuous linear functional `ℝ →L[ℝ] ℝ` is invertible as soon as it does not vanish
at `1`. -/
theorem isInvertible_of_apply_one_ne_zero {T : ℝ →L[ℝ] ℝ} (h : T 1 ≠ 0) : T.IsInvertible := by
  have hTx : ∀ x : ℝ, T x = x * T 1 := by
    intro x
    have h2 := map_smul T x (1 : ℝ)
    rw [smul_eq_mul] at h2
    simpa using h2
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (T 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
  · apply ContinuousLinearMap.ext; intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_apply]
    rw [map_smul, hTx x, smul_eq_mul]
    field_simp
  · apply ContinuousLinearMap.ext; intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_apply]
    rw [hTx x, smul_eq_mul]
    field_simp

/-- For `T : (E × ℝ) →L[ℝ] ℝ`, the shear `v ↦ (T v, v.1)` is invertible as soon as the partial
derivative of `T` in the second variable is invertible. -/
theorem isInvertible_prod_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : (E × ℝ) →L[ℝ] ℝ} (h : (T ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible) :
    (T.prod (ContinuousLinearMap.fst ℝ E ℝ)).IsInvertible := by
  set δL : ℝ →L[ℝ] ℝ := T ∘L ContinuousLinearMap.inr ℝ E ℝ with hδL
  have hδ : δL.IsInvertible := h
  have hsplit : ∀ (x : E) (s : ℝ), T (x, s) = T (x, 0) + δL s := by
    intro x s
    have h1 : (x, s) = (x, 0) + ContinuousLinearMap.inr ℝ E ℝ s := by ext <;> simp
    rw [h1, map_add]
    rfl
  have hself : ∀ r : ℝ, δL (δL.inverse r) = r := by
    intro r
    have := congrArg (fun (f : ℝ →L[ℝ] ℝ) => f r) hδ.self_comp_inverse
    simpa using this
  have hinv : ∀ s : ℝ, δL.inverse (δL s) = s := by
    intro s
    have := congrArg (fun (f : ℝ →L[ℝ] ℝ) => f s) hδ.inverse_comp_self
    simpa using this
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (ContinuousLinearMap.snd ℝ ℝ E).prod
      (δL.inverse ∘L (ContinuousLinearMap.fst ℝ ℝ E
        - (T ∘L ContinuousLinearMap.inl ℝ E ℝ) ∘L ContinuousLinearMap.snd ℝ ℝ E))) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro p
    obtain ⟨r, x⟩ := p
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    change (T (x, δL.inverse (r - T (x, 0))), x) = (r, x)
    rw [hsplit x (δL.inverse (r - T (x, 0))), hself (r - T (x, 0))]
    simp
  · apply ContinuousLinearMap.ext
    intro p
    obtain ⟨x, s⟩ := p
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    change (x, δL.inverse (T (x, s) - T (x, 0))) = (x, s)
    rw [hsplit x s, show T (x, 0) + δL s - T (x, 0) = δL s by ring, hinv s]

/-! ### The local graph form of a regular level set -/

/-- **The zero set of a `C^∞` function on the plane is locally a graph.**  If `h p = 0` and the
partial derivative of `h` at `p` in the direction `eᵢ` does not vanish, then near `p` the set
`{h = 0}` is the graph of a globally `C¹` function `η` over the other coordinate direction `j`:
`y = (y j) • eⱼ + η (y j)`. -/
theorem exists_local_graph_chart {h : E2 → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) {p : E2} (hp : h p = 0)
    (i : Fin 2) (hd : fderiv ℝ h p (e2 i) ≠ 0) :
    ∃ (j : Fin 2) (U : Set E2) (η : ℝ → E2), j ≠ i ∧ IsOpen U ∧ p ∈ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t j = 0) ∧
      (∀ y ∈ U, h y = 0 ↔ y = (y j) • e2 j + η (y j)) := by
  -- pick the other coordinate direction
  obtain ⟨j, hij⟩ : ∃ j : Fin 2, j ≠ i := ⟨if i = 0 then 1 else 0, by fin_cases i <;> decide⟩
  have hji : i ≠ j := hij.symm
  -- the base point of the implicit function theorem
  set x₀ : E2 := p - (p i) • e2 i with hx₀_def
  set u : E2 × ℝ := (x₀, p i) with hu_def
  have hx₀_eq : x₀ = (p j) • e2 j := sub_smul_eq hji p
  -- coordinates: `(x, t) ↦ x + t • eᵢ`
  set lin : E2 × ℝ →L[ℝ] E2 :=
    (ContinuousLinearMap.fst ℝ E2 ℝ) + (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight (e2 i)
    with hlin_def
  have hlin_apply : ∀ z : E2 × ℝ, lin z = z.1 + z.2 • e2 i := by
    intro z; rfl
  have hlin_u : lin u = p := by
    rw [hlin_apply]
    simp only [hu_def, hx₀_def]
    abel
  -- the implicit equation
  set fld : E2 × ℝ → ℝ := fun z => h (lin z) with hfld_def
  have hfld_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fld := hh.comp lin.contDiff
  have hfld_u : fld u = 0 := by
    change h (lin u) = 0
    rw [hlin_u, hp]
  have hflderiv : HasFDerivAt fld (fderiv ℝ fld u) u :=
    ((hfld_cd.contDiffAt (x := u)).differentiableAt (by norm_num)).hasFDerivAt
  have hderiv_fld : fderiv ℝ fld u = (fderiv ℝ h p) ∘L lin := by
    have h1 : HasFDerivAt h (fderiv ℝ h (lin u)) (lin u) :=
      ((hh.differentiable (by norm_num)).differentiableAt).hasFDerivAt
    have h2 : HasFDerivAt lin lin u := lin.hasFDerivAt
    have h3 : HasFDerivAt fld ((fderiv ℝ h (lin u)) ∘L lin) u := by
      have hc := h1.comp u h2
      change HasFDerivAt (fun z => h (lin z)) _ u
      exact hc
    rw [h3.fderiv, hlin_u]
  have hval : fderiv ℝ fld u (0, 1) = fderiv ℝ h p (e2 i) := by
    rw [hderiv_fld, ContinuousLinearMap.comp_apply, hlin_apply]
    simp
  have hif₂ : (fderiv ℝ fld u ∘L ContinuousLinearMap.inr ℝ E2 ℝ).IsInvertible := by
    refine isInvertible_of_apply_one_ne_zero ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hval]
    exact hd
  -- the implicit function data and its local inverse
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hFcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fld u := hfld_cd.contDiffAt
  let φ : ImplicitFunctionData ℝ (E2 × ℝ) ℝ E2 :=
    (hFcd.hasStrictFDerivAt hne).implicitFunctionDataOfProdDomain hif₂
  let Φ : OpenPartialHomeomorph (E2 × ℝ) (ℝ × E2) := φ.toOpenPartialHomeomorph
  have hΦcoe : ⇑Φ = fun z : E2 × ℝ => (fld z, z.1) := by
    funext z
    simp only [Φ, ImplicitFunctionData.toOpenPartialHomeomorph_coe]
    rfl
  have hφpt : φ.pt = u := by
    simp only [φ, HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain]
  have hu_src : u ∈ Φ.source := by
    rw [← hφpt]
    exact φ.pt_mem_toOpenPartialHomeomorph_source
  have hΦapply : ∀ z : E2 × ℝ, Φ z = (fld z, z.1) := fun z => congrFun hΦcoe z
  have hΦu : Φ u = (0, x₀) := by
    rw [hΦapply, hfld_u]
  have hu_tgt : Φ u ∈ Φ.target := Φ.map_source hu_src
  have hx₀_tgt : (0, x₀) ∈ Φ.target := hΦu.symm ▸ hu_tgt
  -- the shear map `G z = (fld z, z.1)`
  set G : E2 × ℝ → ℝ × E2 := fun z => (fld z, z.1) with hG_def
  have hGcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := hfld_cd.prodMk (ContinuousLinearMap.fst ℝ E2 ℝ).contDiff
  have hGfderiv : ∀ z : E2 × ℝ,
      fderiv ℝ G z = (fderiv ℝ fld z).prod (ContinuousLinearMap.fst ℝ E2 ℝ) := by
    intro z
    have h1 : HasFDerivAt fld (fderiv ℝ fld z) z :=
      ((hfld_cd.contDiffAt (x := z)).differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasFDerivAt (fun w : E2 × ℝ => w.1) (ContinuousLinearMap.fst ℝ E2 ℝ) z :=
      hasFDerivAt_fst
    have h3 : HasFDerivAt G ((fderiv ℝ fld z).prod (ContinuousLinearMap.fst ℝ E2 ℝ)) z :=
      h1.prodMk h2
    exact h3.fderiv
  -- the set where `fderiv G` is invertible is open
  have hOopen : IsOpen {z : E2 × ℝ | (fderiv ℝ fld z) (0, 1) ≠ 0} := by
    have hcont : Continuous (fun z : E2 × ℝ => (fderiv ℝ fld z) (0, 1)) :=
      (hfld_cd.continuous_fderiv hne).clm_apply continuous_const
    exact isOpen_ne.preimage hcont
  have huO : u ∈ {z : E2 × ℝ | (fderiv ℝ fld z) (0, 1) ≠ 0} := by
    show (fderiv ℝ fld u) (0, 1) ≠ 0
    rw [hval]; exact hd
  -- `Φ.symm` is `C¹` on a neighbourhood of `Φ u`
  have hΦsymm_u : Φ.symm (Φ u) = u := Φ.left_inv hu_src
  have hcont_symm : ContinuousAt (⇑Φ.symm) (Φ u) := Φ.continuousAt_symm hu_tgt
  have hpre : (⇑Φ.symm ⁻¹' {z : E2 × ℝ | (fderiv ℝ fld z) (0, 1) ≠ 0}) ∈ 𝓝 (Φ u) :=
    hcont_symm.preimage_mem_nhds (hOopen.mem_nhds (hΦsymm_u.symm ▸ huO))
  obtain ⟨T', hT'sub, hT'open, hT'mem⟩ := mem_nhds_iff.mp hpre
  have hsymm_cd : ∀ w ∈ T', w ∈ Φ.target → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Φ.symm) w := by
    intro w hw hwtgt
    have hzO : (fderiv ℝ fld (Φ.symm w)) (0, 1) ≠ 0 := hT'sub hw
    have hinv : (fderiv ℝ G (Φ.symm w)).IsInvertible := by
      rw [hGfderiv]
      exact isInvertible_prod_fst (isInvertible_of_apply_one_ne_zero hzO)
    obtain ⟨e, he⟩ := hinv
    have hfd : HasFDerivAt (⇑Φ) (e : (E2 × ℝ) →L[ℝ] (ℝ × E2)) (⇑Φ.symm w) := by
      rw [hΦcoe]
      have h0 : HasFDerivAt G (fderiv ℝ G (Φ.symm w)) (⇑Φ.symm w) :=
        ((hGcd.contDiffAt (x := ⇑Φ.symm w)).differentiableAt hne).hasFDerivAt
      rw [← he] at h0
      exact h0
    have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Φ) (⇑Φ.symm w) := by
      rw [hΦcoe]; exact hGcd.contDiffAt
    exact Φ.contDiffAt_symm hwtgt hfd hcd
  -- the implicit function of the slice `t = 0`
  let T : Set (ℝ × E2) := T' ∩ Φ.target
  let S : Set E2 := {x : E2 | (0, x) ∈ T}
  have hTopen : IsOpen T := hT'open.inter Φ.open_target
  have hSopen : IsOpen S := by
    have hcont0 : Continuous (fun x : E2 => ((0 : ℝ), x)) := by fun_prop
    exact hTopen.preimage hcont0
  have hx₀S : x₀ ∈ S := by
    refine ⟨?_, hx₀_tgt⟩
    rw [← hΦu]; exact hT'mem
  let ψ : E2 → ℝ := fun x => (Φ.symm ((0 : ℝ), x)).2
  have hψ_cd : ∀ x ∈ S, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ x := by
    intro x hx
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Φ.symm) ((0 : ℝ), x) := hsymm_cd _ hx.1 hx.2
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E2 => (((0 : ℝ), x) : ℝ × E2)) x := by fun_prop
    have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E2 => Φ.symm (((0 : ℝ), x) : ℝ × E2)) x := h1.comp x h2
    exact h3.snd
  -- the graph property on the region where `Φ` and `Φ.symm` are inverse to each other
  have hgraph : ∀ (x : E2) (t : ℝ), (x, t) ∈ Φ.source → (0, x) ∈ Φ.target →
      (fld (x, t) = 0 ↔ t = ψ x) := by
    intro x t hsrc htgt
    have hΦsymm1 : (Φ.symm ((0 : ℝ), x)).1 = x := by
      have h := congrArg Prod.snd (Φ.right_inv htgt)
      rw [hΦapply] at h
      simpa using h
    have hΦsymm_fst : fld (Φ.symm ((0:ℝ), x)) = 0 := by
      have h := congrArg Prod.fst (Φ.right_inv htgt)
      rw [hΦapply] at h
      simpa using h
    have hΦsymm : Φ.symm ((0 : ℝ), x) = (x, ψ x) := by
      have h2 : (Φ.symm ((0:ℝ), x)).2 = ψ x := rfl
      exact Prod.ext hΦsymm1 h2
    constructor
    · intro h0
      have hΦxt : Φ (x, t) = (0, x) := by
        rw [hΦapply, h0]
      have hleft := Φ.left_inv hsrc
      rw [hΦxt, hΦsymm] at hleft
      exact (congrArg Prod.snd hleft).symm
    · intro ht
      have hΦsymm_t : Φ.symm ((0:ℝ), x) = (x, t) := by rw [hΦsymm, ht]
      have hΦxt : Φ (x, t) = (0, x) := by
        rw [← hΦsymm_t]
        exact Φ.right_inv htgt
      have h := congrArg Prod.fst hΦxt
      rw [hΦapply] at h
      simpa using h
  -- the region of the plane carrying the graph
  let PL : E2 → E2 × ℝ := fun y => (y - (y i) • e2 i, y i)
  have hPL_cont : Continuous PL := by fun_prop
  let T₀ : Set (E2 × ℝ) := {z : E2 × ℝ | z ∈ Φ.source ∧ (0, z.1) ∈ Φ.target}
  have hT₀open : IsOpen T₀ := by
    refine Φ.open_source.inter ?_
    exact Φ.open_target.preimage (by fun_prop : Continuous (fun z : E2 × ℝ => ((0 : ℝ), z.1)))
  let V : Set E2 := PL ⁻¹' T₀
  have hVopen : IsOpen V := hT₀open.preimage hPL_cont
  -- the bump function
  obtain ⟨r, hr_pos, hball⟩ := Metric.isOpen_iff.mp hSopen x₀ hx₀S
  set δ : ℝ := r / 4 with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have h3δ_lt : 3 * δ < r := by rw [hδ_def]; linarith
  set β : ContDiffBump (p j) := ⟨2 * δ, 3 * δ, by linarith, by linarith⟩ with hβ_def
  have hβ_in : β.rIn = 2 * δ := rfl
  have hβ_out : β.rOut = 3 * δ := rfl
  have hβ_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (β t : ℝ)) :=
    (β.contDiff (n := ⊤)).of_le (by simp)
  set η : ℝ → E2 := fun t => (β t * ψ (t • e2 j) + (1 - β t) * (p i)) • e2 i with hη_def
  have hηj : ∀ t, η t j = 0 := fun t => e2_smul_apply_ne hji _
  -- `η` is `C¹`
  have hS_mem : ∀ t : ℝ, |t - p j| < r → t • e2 j ∈ S := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    rw [hx₀_eq]
    have hsub : t • e2 j - (p j) • e2 j = (t - p j) • e2 j := by module
    rw [hsub, norm_smul_e2]
    exact ht
  have hψ_comp_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ψ (t • e2 j)) (Metric.ball (p j) r) := by
    rw [Metric.isOpen_ball.contDiffOn_iff]
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ (t • e2 j) := hψ_cd _ (hS_mem t ht)
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => t • e2 j) t := by fun_prop
    have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ ∘ fun t : ℝ => t • e2 j) t := h1.comp t h2
    exact h3
  have hη_on_ball : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η (Metric.ball (p j) r) := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (β t : ℝ)) (Metric.ball (p j) r) := hβ_cd.contDiffOn
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => β t * ψ (t • e2 j)) (Metric.ball (p j) r) :=
      h1.mul hψ_comp_cd
    have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (1 - β t) * (p i)) (Metric.ball (p j) r) :=
      (contDiffOn_const.sub h1).mul contDiffOn_const
    have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => (β t * ψ (t • e2 j) + (1 - β t) * (p i)) • e2 i) (Metric.ball (p j) r) :=
      (h2.add h3).smul contDiffOn_const
    exact h4
  have hη_out : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η {t : ℝ | 3 * δ < |t - p j|} := by
    refine ContDiffOn.congr (contDiffOn_const (c := (p i) • e2 i)) ?_
    intro t ht
    have hβ0 : β t = 0 := by
      apply β.zero_of_le_dist
      rw [hβ_out, Real.dist_eq]
      exact le_of_lt ht
    show (β t * ψ (t • e2 j) + (1 - β t) * (p i)) • e2 i = (p i) • e2 i
    rw [hβ0]; simp
  have hη_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η := by
    refine contDiff_of_contDiffOn_union_of_isOpen hη_on_ball hη_out ?_ Metric.isOpen_ball ?_
    · ext t
      simp only [Set.mem_union, Metric.mem_ball, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      by_cases h : dist t (p j) < r
      · exact Or.inl h
      · right
        have h' : r ≤ dist t (p j) := le_of_not_gt h
        rw [Real.dist_eq] at h'
        show 3 * δ < |t - p j|
        linarith
    · exact isOpen_lt continuous_const (by fun_prop : Continuous (fun t : ℝ => |t - p j|))
  -- the graph property
  have hPL_fst : ∀ y : E2, (PL y).1 = y - (y i) • e2 i := fun y => rfl
  have hPL_snd : ∀ y : E2, (PL y).2 = y i := fun y => rfl
  have hPLp : PL p = u := by
    show (p - (p i) • e2 i, p i) = u
    rw [hu_def, hx₀_def]
  have hchart : ∀ y ∈ V ∩ {y : E2 | |y j - p j| < 2 * δ},
      h y = 0 ↔ y = (y j) • e2 j + η (y j) := by
    intro y hy
    obtain ⟨hyV, hy2⟩ := hy
    have hysrc : PL y ∈ Φ.source := hyV.1
    have hytgt : (0, (PL y).1) ∈ Φ.target := hyV.2
    have hx : y - (y i) • e2 i = (y j) • e2 j := sub_smul_eq hji y
    have hβy : β (y j) = 1 := by
      apply β.one_of_mem_closedBall
      rw [Metric.mem_closedBall, hβ_in, Real.dist_eq]
      exact le_of_lt hy2
    have heta : η (y j) = ψ (y - (y i) • e2 i) • e2 i := by
      show (β (y j) * ψ ((y j) • e2 j) + (1 - β (y j)) * (p i)) • e2 i = _
      rw [hβy, hx]
      simp
    have hhy : h y = fld (y - (y i) • e2 i, y i) := by
      show h y = h (lin (y - (y i) • e2 i, y i))
      congr 1
      rw [hlin_apply, sub_add_cancel]
    have hgf : fld (y - (y i) • e2 i, y i) = 0 ↔ y i = ψ (y - (y i) • e2 i) := by
      have h := hgraph (PL y).1 (PL y).2 hysrc hytgt
      rw [hPL_fst, hPL_snd] at h
      exact h
    have h1 : h y = 0 ↔ y i = ψ (y - (y i) • e2 i) := by
      rw [hhy]
      exact hgf
    have eq1 : (y j) • e2 j + η (y j)
        = (y - (y i) • e2 i) + ψ (y - (y i) • e2 i) • e2 i := by
      rw [← hx, heta]
    have h2 : (y i = ψ (y - (y i) • e2 i)) ↔ y = (y j) • e2 j + η (y j) := by
      constructor
      · intro h
        rw [eq1, show ψ (y - (y i) • e2 i) = y i from h.symm, sub_add_cancel]
      · intro h
        have hy : y = (y - (y i) • e2 i) + ψ (y - (y i) • e2 i) • e2 i := h.trans eq1
        have h5 := congrArg (fun w : E2 => w i) hy
        simpa [e2, PiLp.smul_apply] using h5
    exact h1.trans h2
  refine ⟨j, V ∩ {y : E2 | |y j - p j| < 2 * δ}, η, hij, ?_, ?_, hη_cd, hηj, hchart⟩
  · exact hVopen.inter
      (isOpen_lt (by fun_prop : Continuous (fun y : E2 => |y j - p j|)) continuous_const)
  · refine ⟨?_, ?_⟩
    · show PL p ∈ T₀
      rw [hPLp]
      show u ∈ Φ.source ∧ (0, x₀) ∈ Φ.target
      exact ⟨hu_src, hx₀_tgt⟩
    · show |p j - p j| < 2 * δ
      rw [sub_self, abs_zero]; linarith

/-! ### The main theorem -/

/-- **The truncated regular zero set of a `C^∞` function on the plane has local graph charts.** -/
theorem hasLocalGraphCharts_regular_zeroSet (h : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (R : ℝ)
    (hreg : ∀ z : EuclideanSpace ℝ (Fin 2), h z = 0 → ‖z‖ < R → fderiv ℝ h z ≠ 0) :
    Work.ManifoldParity.HasLocalGraphCharts {z : EuclideanSpace ℝ (Fin 2) | h z = 0 ∧ ‖z‖ < R} := by
  intro x hx
  obtain ⟨hx0, hxR⟩ := hx
  have hd : fderiv ℝ h x ≠ 0 := hreg x hx0 hxR
  have hex : ∃ i : Fin 2, fderiv ℝ h x (e2 i) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hd (by
      ext v
      have hv : v = (v 0) • e2 0 + (v 1) • e2 1 := by
        ext k; fin_cases k <;> simp
      rw [hv, map_add, map_smul, map_smul, hcon 0, hcon 1]
      simp)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨j, U, η, hij, hUopen, hxU, hηcd, hηj, hchart⟩ :=
    exists_local_graph_chart hh hx0 i hi
  refine ⟨j, U ∩ {y : EuclideanSpace ℝ (Fin 2) | ‖y‖ < R}, η, ?_, ⟨hxU, hxR⟩⟩
  refine ⟨hUopen.inter (isOpen_lt continuous_norm continuous_const), hηcd, hηj, ?_⟩
  intro y hy
  obtain ⟨hyU, hyR⟩ := hy
  rw [Work.ManifoldParity.gmap_apply]
  exact ⟨fun h0 => (hchart y hyU).mp h0.1, fun h0 => ⟨(hchart y hyU).mpr h0, hyR⟩⟩

end

end Work.Drive.SmoothGraph

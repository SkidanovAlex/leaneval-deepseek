/-
  `Work.WilE7.Auxiliary.fibreGradMemSpan2` — the single-`a` fibre-conormal-inclusion lemma of
  the E7 fibre-cut argument (BV Lemma 8), used by
  `Submission/Work/WilE7/stratum_j_lt_of_subset_crit.lean`.

  MATHEMATICS
  -----------
  Put `x := projFirst p q z`, `y₀ := projSnd p q z`, and, on the fibre
  `ℝ^q ∋ y ↦ (x, y) ∈ ℝ^{p+q}`,

    * `G y b := eaEval c' (h' b) (x, y)`      (`G y₀ = 0` by `hz`),
    * `F y   := eaEval c  (h a)  (x, y)`      (`F y₀ = 0` by `hvan`).

  Since `eaD` computes the honest partial derivatives, `DG(y₀)` and `DF(y₀)` are the
  "sum of scalars times coordinate projections" continuous linear maps whose coefficients are
  exactly the numbers occurring in the statement.  `hrank` says the `j' × q` matrix of
  `DG(y₀)` has full row rank `j'`; by finite-dimensional duality this makes `DG(y₀)` onto, so
  near `y₀` the level set `{G = 0}` is a submanifold with tangent space `ker DG(y₀)`.  `hvan`
  says `F` vanishes on it, so `ker DG(y₀) ≤ ker DF(y₀)`
  (`kerLeKerOfVanishOnLevelSet`, proved below from the implicit function theorem), and the
  linear-algebra fact "a linear form vanishing on `⋂ ker Lᵢ` lies in the span of the `Lᵢ`"
  (`mem_span_of_iInf_ker_le_ker`) produces the multipliers `lam`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt
import Submission.Work.WilE9.EaD.eaEval_contDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE7.Auxiliary

open WilkiesDesign WilkiesDesign.E Work.WilE5

/-! ## A general submersion / level-set lemma

If a map `g` is strictly differentiable at `y₀` with a *surjective* derivative `L`, and a
function `F` (differentiable at `y₀` with derivative `M`) is constant on the level set
`{g = 0}` near `y₀`, then `ker L ≤ ker M`.

The proof paramatrises the level set with the implicit function theorem
(`HasStrictFDerivAt.implicitFunction`): the `G`erm of the level set through `y₀` is the image
of the strictly differentiable chart `φ (g y₀) : ker L → ℝ^q` whose derivative at `0` is the
inclusion `ker L ↪ ℝ^q` (Mathlib's `HasStrictFDerivAt.to_implicitFunction`).  Restricting to
the line `t ↦ t • w` for `w ∈ ker L` gives a curve through `y₀` inside the level set, tangent
to `w`; `F` is constant along it, and differentiating twice (once through `F`'s derivative,
once as a constant) gives `M w = 0`. -/
private theorem kerLeKerOfVanishOnLevelSet {q k : ℕ} (g : (Fin q → ℝ) → (Fin k → ℝ))
    (F : (Fin q → ℝ) → ℝ) (y₀ : Fin q → ℝ) (L : (Fin q → ℝ) →L[ℝ] (Fin k → ℝ))
    (M : (Fin q → ℝ) →L[ℝ] ℝ)
    (hg : HasStrictFDerivAt g L y₀) (hF : HasFDerivAt F M y₀)
    (hsurj : L.range = ⊤) (hg0 : g y₀ = 0)
    (hvan : ∀ᶠ y in nhds y₀, g y = 0 → F y = F y₀) :
    L.ker ≤ M.ker := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  let w : L.ker := ⟨x, hx⟩
  -- `t ↦ t • w` is continuous at `0`.
  have htw : Tendsto (fun t : ℝ => t • w) (𝓝 (0 : ℝ)) (𝓝 (0 : L.ker)) := by
    simpa using (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).smul_const w
  -- The implicit function theorem parametrises the level set by `ker L`.
  let φ : (Fin k → ℝ) → L.ker → (Fin q → ℝ) := hg.implicitFunction g L hsurj
  have hφ0 : φ (g y₀) 0 = y₀ := hg.implicitFunction_apply_image hsurj
  have hφdiff : HasStrictFDerivAt (φ (g y₀)) L.ker.subtypeL 0 := hg.to_implicitFunction hsurj
  let γ : ℝ → (Fin q → ℝ) := fun t => φ (g y₀) (t • w)
  have hγ0 : γ 0 = y₀ := by simp [γ, hφ0]
  have hγcont : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 y₀) := by
    have h := hg.tendsto_implicitFunction hsurj (tendsto_const_nhds (x := g y₀)) htw
    simpa [γ, Function.comp_def, hγ0] using h
  -- `γ` lands in the level set of `g`.
  have hgγ : ∀ᶠ t in 𝓝 (0 : ℝ), g (γ t) = 0 := by
    have hmap := hg.map_implicitFunction_eq hsurj
    have htend : Tendsto (fun t : ℝ => (g y₀, t • w)) (𝓝 (0 : ℝ)) (𝓝 (g y₀, (0 : L.ker))) :=
      (tendsto_const_nhds (x := g y₀)).prodMk_nhds htw
    filter_upwards [htend.eventually hmap] with t ht
    simp only [γ] at ⊢
    rw [ht, hg0]
  -- hence `F` is constant along `γ`.
  have hFconst : (F ∘ γ) =ᶠ[𝓝 (0 : ℝ)] (fun _ => F y₀) := by
    filter_upwards [hγcont.eventually hvan, hgγ] with t ht hgt
    exact ht hgt
  -- the derivative of `γ` at `0` is `w = x`.
  have hder : HasDerivAt (fun t : ℝ => t • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hderivγ : HasDerivAt γ x 0 := by
    have hFd : HasFDerivAt (φ (g y₀)) L.ker.subtypeL ((fun t : ℝ => t • w) 0) := by
      simpa using hφdiff.hasFDerivAt
    have h1 := hFd.comp_hasDerivAt (0 : ℝ) hder
    have hsub : L.ker.subtypeL w = x := rfl
    simpa [γ, Function.comp_def, hsub] using h1
  -- differentiate `F ∘ γ` two ways.
  have hFγ : HasFDerivAt F M (γ 0) := by rw [hγ0]; exact hF
  have hd1 : HasDerivAt (F ∘ γ) (M x) 0 := hFγ.comp_hasDerivAt (0 : ℝ) hderivγ
  have hd2 : HasDerivAt (F ∘ γ) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (F y₀)).congr_of_eventuallyEq hFconst
  exact hd1.unique hd2

/-! ## Full row rank means the coordinate forms span -/

/-- The continuous linear map `x ↦ fun b => ∑ l, A b l * x l` (i.e. multiplication by the
matrix `A` acting on the right) has full range as soon as the matrix has maximal rank `m`. -/
private theorem piRangeTopOfRank {m q : ℕ} (A : Fin m → Fin q → ℝ)
    (hrank : (Matrix.of A).rank = m) :
    (ContinuousLinearMap.pi (fun b : Fin m =>
      (∑ l : Fin q, A b l • (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ)))).range
      = ⊤ := by
  let f : (Fin q → ℝ) →L[ℝ] (Fin m → ℝ) := ContinuousLinearMap.pi (fun b : Fin m =>
      (∑ l : Fin q, A b l • (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ)))
  have hcoe : (f : (Fin q → ℝ) →ₗ[ℝ] (Fin m → ℝ)) = (Matrix.of A).mulVecLin := by
    ext v b
    simp [f, ContinuousLinearMap.coe_pi, LinearMap.pi_apply, Matrix.mulVec, dotProduct]
  show f.range = ⊤
  rw [show f.range = LinearMap.range (f : (Fin q → ℝ) →ₗ[ℝ] (Fin m → ℝ)) from rfl, hcoe]
  apply Submodule.eq_top_of_finrank_eq
  rw [Matrix.rank] at hrank
  rw [hrank]
  simp

/-! ## The fibre inclusion `y ↦ (x, y)` and its strict derivative -/

/-- The linear map `y ↦ Fin.append 0 y`: the inclusion of the `q` fibre coordinates into
`ℝ^{p+q}`, i.e. the linear part of `y ↦ Fin.append x y`. -/
private def fibCLM (p q : ℕ) : (Fin q → ℝ) →L[ℝ] (Fin (p + q) → ℝ) :=
  ContinuousLinearMap.pi fun s : Fin (p + q) =>
    Fin.append (fun _ : Fin p => (0 : (Fin q → ℝ) →L[ℝ] ℝ))
      (fun l : Fin q => (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ)) s

@[simp] private theorem fibCLM_apply (p q : ℕ) (y : Fin q → ℝ) :
    fibCLM p q y = Fin.append (0 : Fin p → ℝ) y := by
  ext s
  refine Fin.addCases (fun i => ?_) (fun l => ?_) s <;>
    simp [fibCLM, ContinuousLinearMap.pi_apply]

/-- The affine map `y ↦ Fin.append x y` is strictly differentiable, with linear part `fibCLM`. -/
private theorem hasStrictFDerivAt_fibAppend (p q : ℕ) (x : Fin p → ℝ) (y₀ : Fin q → ℝ) :
    HasStrictFDerivAt (fun y : Fin q → ℝ => Fin.append x y) (fibCLM p q) y₀ := by
  have h1 : HasStrictFDerivAt (fun y : Fin q → ℝ => Fin.append x 0 + fibCLM p q y)
      (fibCLM p q) y₀ :=
    (fibCLM p q).hasStrictFDerivAt.const_add (Fin.append x (0 : Fin q → ℝ))
  have hfun : (fun y : Fin q → ℝ => Fin.append x 0 + fibCLM p q y)
      = fun y : Fin q → ℝ => Fin.append x y := by
    funext y
    ext s
    rw [Pi.add_apply, fibCLM_apply]
    refine Fin.addCases (fun i => ?_) (fun l => ?_) s <;> simp
  rwa [hfun] at h1

/-- The derivative of `y ↦ eaEval c Q (Fin.append x y)` in the fibre directions, as a strict
derivative (so that the implicit function theorem applies). -/
private theorem eaEval_fibAppend_hasStrictFDerivAt {p q r : ℕ} (c : EAChain (p + q) r)
    (Q : EAPoly (p + q) r) (x : Fin p → ℝ) (y₀ : Fin q → ℝ) :
    HasStrictFDerivAt (fun y : Fin q → ℝ => eaEval c Q (Fin.append x y))
      (∑ d : Fin q, eaEval c (eaD c (Fin.natAdd p d) Q) (Fin.append x y₀) •
        (ContinuousLinearMap.proj d : (Fin q → ℝ) →L[ℝ] ℝ)) y₀ := by
  set D : (Fin (p + q) → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin (p + q), eaEval c (eaD c i Q) (Fin.append x y₀) •
      (ContinuousLinearMap.proj i : (Fin (p + q) → ℝ) →L[ℝ] ℝ) with hD
  have heval : HasStrictFDerivAt (fun w : Fin (p + q) → ℝ => eaEval c Q w) D
      (Fin.append x y₀) := by
    refine ContDiffAt.hasStrictFDerivAt' (Work.WilE9.EaD.eaEval_contDiff c Q).contDiffAt ?_ ?_
    · simpa only [hD] using Work.WilE9.EaD.eaD_hasFDerivAt c Q (Fin.append x y₀)
    · simp
  have hcomp := heval.comp y₀ (hasStrictFDerivAt_fibAppend p q x y₀)
  have hCLM : ContinuousLinearMap.comp D (fibCLM p q)
      = ∑ d : Fin q, eaEval c (eaD c (Fin.natAdd p d) Q) (Fin.append x y₀) •
          (ContinuousLinearMap.proj d : (Fin q → ℝ) →L[ℝ] ℝ) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, hD, fibCLM_apply]
    rw [Fin.sum_univ_add]
    simp
  rwa [hCLM] at hcomp

/-- Evaluating "sum of scalars times coordinate projections" on a coordinate unit vector. -/
private theorem sum_smul_proj_single {q : ℕ} (f : Fin q → ℝ) (d : Fin q) :
    (∑ d' : Fin q, f d' • (ContinuousLinearMap.proj d' : (Fin q → ℝ) →L[ℝ] ℝ))
      (Pi.single d 1) = f d := by
  rw [ContinuousLinearMap.sum_apply]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single d]
  · simp
  · intro d' _ hne
    simp [Pi.single_eq_of_ne hne]
  · intro hd
    exact absurd (Finset.mem_univ d) hd

/-! ## The target lemma -/

theorem fibreGradMemSpan2 {p q : ℕ} {j j' r r' : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (c' : WilkiesDesign.E.EAChain (p + q) r') (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r)
    (h' : Fin j' → WilkiesDesign.E.EAPoly (p + q) r') (a : Fin j) (z : Fin (p + q) → ℝ)
    (hz : ∀ b, WilkiesDesign.E.eaEval c' (h' b) z = 0)
    (hrank : (Matrix.of fun (b : Fin j') (l : Fin q) =>
        WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z).rank = j')
    (hvan : ∀ᶠ y in nhds (WilkiesDesign.E.projSnd p q z),
        (∀ b, WilkiesDesign.E.eaEval c' (h' b) (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0) →
        WilkiesDesign.E.eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0) :
    ∃ lam : Fin j' → ℝ, ∀ l : Fin q,
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a)) z
      = ∑ b, lam b * WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z
    := by
  classical
  have happ : Fin.append (projFirst p q z) (projSnd p q z) = z := by
    unfold WilkiesDesign.E.projFirst WilkiesDesign.E.projSnd
    exact Fin.append_castAdd_natAdd
  set A : Fin j' → Fin q → ℝ := fun b l => eaEval c' (eaD c' (yDir p l) (h' b)) z with hA
  set Dv : Fin q → ℝ := fun l => eaEval c (eaD c (yDir p l) (h a)) z with hDv
  set G : (Fin q → ℝ) → (Fin j' → ℝ) :=
    fun y b => eaEval c' (h' b) (Fin.append (projFirst p q z) y) with hG
  set Ff : (Fin q → ℝ) → ℝ := fun y => eaEval c (h a) (Fin.append (projFirst p q z) y) with hFf
  set L : (Fin q → ℝ) →L[ℝ] (Fin j' → ℝ) :=
    ContinuousLinearMap.pi (fun b => ∑ l : Fin q, A b l •
      (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ)) with hL
  set M : (Fin q → ℝ) →L[ℝ] ℝ :=
    ∑ l : Fin q, Dv l • (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ) with hM
  -- `G y₀ = 0`
  have hG0 : G (projSnd p q z) = 0 := by
    funext b
    simp only [hG, happ]
    exact hz b
  -- `F y₀ = 0`
  have hF0 : Ff (projSnd p q z) = 0 := by
    have h1 : (∀ b, eaEval c' (h' b) (Fin.append (projFirst p q z) (projSnd p q z)) = 0) := by
      intro b; rw [happ]; exact hz b
    have h2 := hvan.self_of_nhds h1
    rw [happ] at h2
    simpa only [hFf, happ] using h2
  -- `F` is locally constant on the level set of `G` through `y₀`
  have hvan' : ∀ᶠ y in nhds (projSnd p q z), G y = 0 → Ff y = Ff (projSnd p q z) := by
    filter_upwards [hvan] with y hy
    intro hGy
    have h1 : ∀ b, eaEval c' (h' b) (Fin.append (projFirst p q z) y) = 0 := by
      intro b; simpa only [hG, Pi.zero_apply] using congrFun hGy b
    have h3 := hy h1
    rw [hF0]
    simpa only [hFf] using h3
  -- strict differentiability of `G` on the fibre, with derivative `L`
  have hGs : HasStrictFDerivAt G L (projSnd p q z) := by
    rw [hL, hG]
    rw [hasStrictFDerivAt_pi]
    intro b
    have hb := eaEval_fibAppend_hasStrictFDerivAt c' (h' b) (projFirst p q z) (projSnd p q z)
    simpa only [hA, yDir, happ] using hb
  -- strict differentiability of `F` on the fibre, with derivative `M`
  have hFs : HasStrictFDerivAt Ff M (projSnd p q z) := by
    rw [hM, hFf]
    have hb := eaEval_fibAppend_hasStrictFDerivAt c (h a) (projFirst p q z) (projSnd p q z)
    simpa only [hDv, yDir, happ] using hb
  have hF : HasFDerivAt Ff M (projSnd p q z) := hFs.hasFDerivAt
  -- full rank of `DG(y₀)` gives surjectivity
  have hsurj : L.range = ⊤ := by
    rw [hL]
    exact piRangeTopOfRank A (by simpa only [hA] using hrank)
  -- tangent space of the level set lies in `ker DF(y₀)`
  have hkerincl : L.ker ≤ M.ker :=
    kerLeKerOfVanishOnLevelSet G Ff (projSnd p q z) L M hGs hF hsurj hG0 hvan'
  -- linear algebra: `M` is a linear combination of the coordinate forms `v ↦ (L v) b`
  have hle : ⨅ b : Fin j', LinearMap.ker (((ContinuousLinearMap.proj b).comp L).toLinearMap)
      ≤ LinearMap.ker M.toLinearMap := by
    intro v hv
    rw [LinearMap.mem_ker]
    simp only [Submodule.mem_iInf] at hv
    have hv' : ∀ b, L v b = 0 := by
      intro b
      have hb := hv b
      simpa using hb
    have hLv : v ∈ L.ker := by
      show L v = 0
      funext b; exact hv' b
    exact hkerincl hLv
  have hmem : M.toLinearMap ∈ Submodule.span ℝ
      (Set.range (fun b : Fin j' => ((ContinuousLinearMap.proj b).comp L).toLinearMap)) :=
    mem_span_of_iInf_ker_le_ker hle
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨lam, fun l => ?_⟩
  have h3l : (∑ b, lam b * L (Pi.single l 1) b) = M (Pi.single l 1) := by
    have h := LinearMap.congr_fun hlam (Pi.single l 1)
    rw [LinearMap.sum_apply] at h
    simpa using h
  have hMl : M (Pi.single l 1) = Dv l := by
    rw [hM]
    exact sum_smul_proj_single Dv l
  have hLl : ∀ b, L (Pi.single l 1) b = A b l := by
    intro b
    rw [hL]
    simp only [ContinuousLinearMap.pi_apply]
    exact sum_smul_proj_single (A b) l
  have hfin : Dv l = ∑ b, lam b * A b l := by
    calc Dv l = M (Pi.single l 1) := hMl.symm
      _ = ∑ b, lam b * L (Pi.single l 1) b := h3l.symm
      _ = ∑ b, lam b * A b l := Finset.sum_congr rfl (fun b _ => by rw [hLl b])
  simpa only [hDv, hA] using hfin

end Work.WilE7.Auxiliary

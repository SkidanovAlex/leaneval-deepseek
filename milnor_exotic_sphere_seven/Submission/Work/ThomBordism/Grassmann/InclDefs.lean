import Submission.Work.ThomBordism.Grassmann.Oriented

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The stabilisation inclusion `G̃r_k(ℝ^{k+m}) ↪ G̃r_k(ℝ^{k+m+1})` and its chart bookkeeping

Appending a last coordinate `x ↦ (x,0)` embeds `ℝ^{k+m}` into `ℝ^{k+m+1}` as a linear isometry;
it carries orthonormal frames to orthonormal frames, is `SO(k)`-equivariant, and therefore descends
to a continuous map `ogIncl : OG k m → OG k (m+1)` of oriented Grassmannians.

The rest of the module is the **chart bookkeeping** needed to compare the tautological bundle on
`OG k (m+1)` with the one on `OG k m`.  Since `Finset.equivFinOfCardEq` is an opaque choice, a chart
`i` of `G̃r_k(ℝ^{k+m+1})` whose finset does not contain the last coordinate and the corresponding
chart `chartDown i h` of `G̃r_k(ℝ^{k+m})` have *unrelated* enumerations; the relation is a
permutation `chartPerm i h` of `Fin k`, and the central computation is

`frameMatrix i (inclFrame f) = (frameMatrix (chartDown i h) f).submatrix (chartPerm i h) id`,

i.e. the two frame matrices differ by the row permutation `chartPerm i h`.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

/-! ## Appending a coordinate -/

/-- Append the coordinate `0`: the map `ℝⁿ → ℝⁿ⁺¹`, `x ↦ (x,0)`. -/
def snoc0 (n : ℕ) (y : Amb n) : Amb (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i : Fin n => y.ofLp i) 0)

@[simp] theorem snoc0_ofLp_castSucc (n : ℕ) (y : Amb n) (j : Fin n) :
    (snoc0 n y).ofLp j.castSucc = y.ofLp j := by simp [snoc0]

@[simp] theorem snoc0_ofLp_last (n : ℕ) (y : Amb n) :
    (snoc0 n y).ofLp (Fin.last n) = 0 := by simp [snoc0]

theorem snoc0_norm_sq (n : ℕ) (y : Amb n) : ‖snoc0 n y‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_castSucc]
  simp only [snoc0, WithLp.ofLp_toLp, Fin.snoc_castSucc, Fin.snoc_last]
  rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ), Real.norm_eq_abs, sq_abs]
  ring

/-- `snoc0` as a linear map. -/
def snoc0LM (n : ℕ) : Amb n →ₗ[ℝ] Amb (n + 1) where
  toFun := snoc0 n
  map_add' x y := by
    apply PiLp.ext
    intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp [snoc0]
  map_smul' c x := by
    apply PiLp.ext
    intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp [snoc0]

/-- **Appending a zero coordinate, as a linear isometry** `ℝⁿ ↪ ℝⁿ⁺¹`. -/
def snoc0LI (n : ℕ) : Amb n →ₗᵢ[ℝ] Amb (n + 1) where
  toLinearMap := snoc0LM n
  norm_map' y := by
    have h := snoc0_norm_sq n y
    have h2 : ‖snoc0LM n y‖ = ‖snoc0 n y‖ := rfl
    rw [h2]
    nlinarith [norm_nonneg (snoc0 n y), norm_nonneg y]

theorem snoc0LI_apply (n : ℕ) (y : Amb n) : snoc0LI n y = snoc0 n y := rfl

theorem snoc0LI_inner (n : ℕ) (x y : Amb n) :
    inner ℝ (snoc0LI n x) (snoc0LI n y) = inner ℝ x y :=
  (snoc0LI n).inner_map_map x y

/-! ## The induced map on frames and Grassmannians -/

/-- **The frame inclusion**: append a zero coordinate to every vector of an orthonormal frame. -/
def inclFrame (k m : ℕ) (f : Stiefel k m) : Stiefel k (m + 1) :=
  ⟨fun j => snoc0LI (k + m) (f.1 j), by
    have h := f.2
    rw [orthonormal_iff_ite] at h
    rw [orthonormal_iff_ite]
    intro i j
    rw [snoc0LI_inner]
    exact h i j⟩

@[simp] theorem inclFrame_val (k m : ℕ) (f : Stiefel k m) (j : Fin k) :
    (inclFrame k m f).1 j = snoc0LI (k + m) (f.1 j) := rfl

theorem continuous_inclFrame (k m : ℕ) : Continuous (inclFrame (k := k) (m := m)) := by
  refine Continuous.subtype_mk ?_ ?_
  exact continuous_pi (fun j => (snoc0LI (k + m)).continuous.comp
    ((continuous_apply j).comp continuous_subtype_val))

/-- **The frame inclusion is `SO(k)`-equivariant.** -/
theorem inclFrame_soAct (k m : ℕ) (A : SOk k) (f : Stiefel k m) :
    inclFrame k m (A.act f) = A.act (inclFrame k m f) := by
  apply Subtype.ext
  funext i
  show snoc0LI (k + m) (soActFun A.1 f.1 i)
      = soActFun (m := m + 1) A.1 (fun j => snoc0LI (k + m) (f.1 j)) i
  simp only [soActFun]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])

/-- **The stabilisation map of oriented Grassmannians**, induced by appending a zero coordinate. -/
def ogIncl (k m : ℕ) : OG k m → OG k (m + 1) :=
  Quotient.lift (fun f : Stiefel k m => Quotient.mk'' (inclFrame k m f)) (fun f g hfg => by
    obtain ⟨A, rfl⟩ := hfg
    rw [inclFrame_soAct]
    exact Quotient.sound (show (grassmannSetoid k (m + 1)).r (inclFrame k m f)
      (A.act (inclFrame k m f)) from ⟨A, rfl⟩))

@[simp] theorem ogIncl_mk (k m : ℕ) (f : Stiefel k m) :
    ogIncl k m (Quotient.mk'' f) = Quotient.mk'' (inclFrame k m f) := rfl

theorem continuous_ogIncl (k m : ℕ) : Continuous (ogIncl k m) := by
  refine (isQuotientMap_quotient_mk'.continuous_iff).mpr ?_
  show Continuous (fun f : Stiefel k m => Quotient.mk'' (inclFrame k m f))
  exact continuous_quotient_mk'.comp (continuous_inclFrame k m)

/-- The stabilisation map as a continuous map. -/
def ogInclCM (k m : ℕ) : C(OG k m, OG k (m + 1)) :=
  ⟨ogIncl k m, continuous_ogIncl k m⟩

@[simp] theorem ogInclCM_apply (k m : ℕ) (x : OG k m) : ogInclCM k m x = ogIncl k m x := rfl

/-! ## The chart bookkeeping -/

/-- The chart of `G̃r_k(ℝ^{k+m})` obtained from a chart `i` of `G̃r_k(ℝ^{k+m+1})` that avoids the
last coordinate, by dropping that coordinate. -/
def chartDownFinset (k m : ℕ) (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    Finset (Fin (k + m)) :=
  i.1.preimage Fin.castSucc (Fin.castSucc_injective (k + m)).injOn

@[simp] theorem mem_chartDownFinset {i : ChartIdx k (m + 1)} {h : Fin.last (k + m) ∉ i.1}
    {j : Fin (k + m)} : j ∈ chartDownFinset k m i h ↔ Fin.castSucc j ∈ i.1 :=
  Finset.mem_preimage

theorem card_chartDownFinset (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    (chartDownFinset k m i h).card = k := by
  have hmap : (chartDownFinset k m i h).map Fin.castSuccEmb = i.1 := by
    ext x
    rw [Finset.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [Fin.castSuccEmb_apply, mem_chartDownFinset] using hy
    · intro hx
      have hne : x ≠ Fin.last (k + m) := fun hh => h (hh ▸ hx)
      have hval : x.val ≠ k + m := fun hh => hne (Fin.ext hh)
      have hlt : x.val < k + m := by have := x.isLt; omega
      refine ⟨⟨x.val, hlt⟩, ?_, ?_⟩
      · rw [mem_chartDownFinset]
        show Fin.castSucc (⟨x.val, hlt⟩ : Fin (k + m)) ∈ i.1
        rw [show Fin.castSucc (⟨x.val, hlt⟩ : Fin (k + m)) = x from Fin.ext rfl]
        exact hx
      · exact Fin.ext rfl
  calc (chartDownFinset k m i h).card
      = ((chartDownFinset k m i h).map Fin.castSuccEmb).card := (Finset.card_map _).symm
    _ = i.1.card := by rw [hmap]
    _ = k := i.2

/-- **The chart of `G̃r_k(ℝ^{k+m})` corresponding to a chart `i` of `G̃r_k(ℝ^{k+m+1})` avoiding
the last coordinate.** -/
def chartDown (k m : ℕ) (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) : ChartIdx k m :=
  ⟨chartDownFinset k m i h, card_chartDownFinset i h⟩

@[simp] theorem chartDown_val (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    (chartDown k m i h).1 = chartDownFinset k m i h := rfl

/-- The `jj`-th row of the frame matrix of `i` (read in the big ambient space) is the
coordinate `chartVal i jj`. -/
def chartVal (k m : ℕ) (i : ChartIdx k (m + 1)) (jj : Fin k) : Fin (k + m + 1) :=
  (((i.1.equivFinOfCardEq i.2).symm jj) : Fin (k + m + 1))

theorem chartVal_mem (i : ChartIdx k (m + 1)) (jj : Fin k) : chartVal k m i jj ∈ i.1 :=
  ((i.1.equivFinOfCardEq i.2).symm jj).2

theorem chartVal_ne_last (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) (jj : Fin k) :
    chartVal k m i jj ≠ Fin.last (k + m) :=
  fun hh => h (hh ▸ chartVal_mem i jj)

theorem chartVal_lt (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) (jj : Fin k) :
    (chartVal k m i jj).val < k + m := by
  have h1 := (chartVal k m i jj).isLt
  have h2 : (chartVal k m i jj).val ≠ k + m := fun hh => chartVal_ne_last i h jj (Fin.ext hh)
  omega

/-- The same coordinate, now read in the small ambient space `ℝ^{k+m}`. -/
def chartVal' (k m : ℕ) (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1)
    (jj : Fin k) : Fin (k + m) :=
  ⟨(chartVal k m i jj).val, chartVal_lt i h jj⟩

theorem chartVal_castSucc (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) (jj : Fin k) :
    Fin.castSucc (chartVal' k m i h jj) = chartVal k m i jj := Fin.ext rfl

/-- **The permutation relating the enumeration of the big chart `i` to that of the small chart
`chartDown i h`.** -/
def chartPermFun (k m : ℕ) (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) (jj : Fin k) :
    Fin k :=
  ((chartDown k m i h).1.equivFinOfCardEq (chartDown k m i h).2)
    ⟨chartVal' k m i h jj, show chartVal' k m i h jj ∈ chartDownFinset k m i h from by
      rw [mem_chartDownFinset, chartVal_castSucc]
      exact chartVal_mem i jj⟩

theorem chartPermFun_spec (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) (jj : Fin k) :
    Fin.castSucc (((chartDown k m i h).1.equivFinOfCardEq (chartDown k m i h).2).symm
        (chartPermFun k m i h jj)) = chartVal k m i jj := by
  rw [chartPermFun, Equiv.symm_apply_apply]
  exact chartVal_castSucc i h jj

theorem chartPermFun_injective (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    Function.Injective (chartPermFun k m i h) := by
  intro a b hab
  have h1 : (⟨chartVal' k m i h a, _⟩ : ↥(chartDown k m i h).1)
      = ⟨chartVal' k m i h b, _⟩ :=
    ((chartDown k m i h).1.equivFinOfCardEq (chartDown k m i h).2).injective hab
  have h2 : (chartVal' k m i h a : Fin (k + m)) = chartVal' k m i h b := congrArg Subtype.val h1
  have h3 : chartVal k m i a = chartVal k m i b := by
    rw [← chartVal_castSucc i h a, ← chartVal_castSucc i h b, h2]
  have h4 : ((i.1.equivFinOfCardEq i.2).symm a : Fin (k + m + 1))
      = ((i.1.equivFinOfCardEq i.2).symm b : Fin (k + m + 1)) := h3
  exact (i.1.equivFinOfCardEq i.2).symm.injective (Subtype.ext h4)

/-- **The permutation matrix relating the two chart enumerations** (as an `Equiv.Perm`). -/
def chartPerm (k m : ℕ) (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    Equiv.Perm (Fin k) :=
  Equiv.ofBijective (chartPermFun k m i h) (by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨chartPermFun_injective i h, rfl⟩)

@[simp] theorem chartPerm_apply (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1)
    (jj : Fin k) : chartPerm k m i h jj = chartPermFun k m i h jj := rfl

theorem chartPerm_spec (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) (jj : Fin k) :
    Fin.castSucc ((↑(((chartDown k m i h).1.equivFinOfCardEq (chartDown k m i h).2).symm
        (chartPerm k m i h jj)) : Fin (k + m))) = chartVal k m i jj := by
  rw [chartPerm_apply]
  exact chartPermFun_spec i h jj

/-- The permutation matrix of `chartPerm i h`. -/
def chartQ (k m : ℕ) (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    Matrix (Fin k) (Fin k) ℝ :=
  (chartPerm k m i h).permMatrix ℝ

/-- The inverse of the permutation matrix of `chartPerm i h`. -/
def chartQinv (k m : ℕ) (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    Matrix (Fin k) (Fin k) ℝ :=
  ((chartPerm k m i h)⁻¹).permMatrix ℝ

theorem chartQ_mul_chartQinv (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    chartQ k m i h * chartQinv k m i h = 1 := by
  rw [chartQ, chartQinv, ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

theorem chartQinv_mul_chartQ (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    chartQinv k m i h * chartQ k m i h = 1 := by
  rw [chartQ, chartQinv, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

/-- The entry formula for a frame matrix: the `(jj,mm)` entry is the `mm`-th frame vector read
at the coordinate `e_S.symm jj`. -/
theorem frameMatrix_apply {S : ChartIdx k m} (g : Fin k → Amb (k + m)) (jj mm : Fin k) :
    frameMatrix S g jj mm
      = (g mm).ofLp (((S.1.equivFinOfCardEq S.2).symm jj : ↥S.1) : Fin (k + m)) := by
  rw [frameMatrix]
  exact PiLp.proj_apply 2 (fun _ : Fin (k + m) => ℝ) _ (g mm)

/-- **The central chart computation**: the frame matrix of an included frame in the big chart `i`
is the frame matrix in the corresponding small chart `chartDown i h`, with its rows permuted by
`chartPerm i h`. -/
theorem frameMatrix_inclFrame (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1)
    (f : Stiefel k m) :
    frameMatrix i (inclFrame k m f).1
      = (frameMatrix (chartDown k m i h) f.1).submatrix (chartPerm k m i h) id := by
  ext jj mm
  rw [Matrix.submatrix_apply, frameMatrix_apply, frameMatrix_apply, inclFrame_val,
    show snoc0LI (k + m) (f.1 mm) = snoc0 (k + m) (f.1 mm) from rfl,
    show (↑((i.1.equivFinOfCardEq i.2).symm jj) : Fin (k + m + 1)) = chartVal k m i jj
      from rfl,
    ← chartVal_castSucc i h jj, snoc0_ofLp_castSucc]
  have hz : (↑(((chartDown k m i h).1.equivFinOfCardEq (chartDown k m i h).2).symm
        (chartPerm k m i h jj)) : Fin (k + m)) = chartVal' k m i h jj := by
    have h1 : Fin.castSucc (↑(((chartDown k m i h).1.equivFinOfCardEq (chartDown k m i h).2).symm
        (chartPerm k m i h jj)) : Fin (k + m)) = chartVal k m i jj := chartPerm_spec i h jj
    have h2 : Fin.castSucc (chartVal' k m i h jj) = chartVal k m i jj := chartVal_castSucc i h jj
    exact Fin.castSucc_injective (k + m) (h1.trans h2.symm)
  simp only [id_eq]
  rw [hz]

end

end Work.ThomBordism.Grassmann

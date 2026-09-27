import Mathlib
import Submission.Work.Drive.intersection_triple
import Submission.Work.Drive.TripleMeetDefs
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.ManifoldParity.InterSetDefs
import Submission.Work.Drive.ManifoldParity.FlowSetupDefs
import Submission.Work.Drive.ManifoldParity.GraphMap

/-!
# Basic vocabulary for the manifold triple-intersection parity

Setting for `Work.Drive.manifold_triple_inter_boundary_parity`: three smooth maps
`D 0, D 1, D 2 : ℝ³ → M` into a smooth `4`-manifold.

* `bPartC k` is the `k`-th block projection `ℝ⁹ → ℝ³` as a continuous linear map, `mk3 v` the
  corresponding point of `ℝ⁹`, and `tripleEquiv` the identification of `ℝ⁹` with
  `Fin 3 → ℝ³`;
* `region3 p D` and `chartDiff3 p D` are the region of the chart at `p` on which all three chains
  take their values in its source, and the *charted difference map*
  `x ↦ (φ (D₀ x₀) − φ (D₁ x₁), φ (D₀ x₀) − φ (D₂ x₂))` (as an element of `ℝ⁸` through `pairUp`);
* `K3 D`, `bK3 D` and `S3 D k` are the triple intersection set in the nine-box, its part on the
  boundary of the nine-box, and its part whose `k`-th block is on a face — the manifold form of
  `Work.Drive.tripleMeet`, `Work.Drive.bdyZeros (tripleDiff V)` and `Work.Drive.blockMeet V k`.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## The stacking map of two `ℝ⁴`s -/

/-- The stacking of two vectors of `ℝ⁴` into a vector of `ℝ⁸` (the map of
`Work.Drive.pairUp`, whose coordinate lemmas we use). -/
abbrev pUp (a b : Tgt 4) : Tgt 8 := Work.Drive.pairUp a b

/-- The stacking map as a continuous linear map on the product. -/
def pUpCLM : (Tgt 4 × Tgt 4) →L[ℝ] Tgt 8 :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 8 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 8 =>
      if h : (i : ℕ) < 4 then
        (PiLp.proj 2 (fun _ : Fin 4 => ℝ) ⟨i.val, h⟩).comp
          (ContinuousLinearMap.fst ℝ (Tgt 4) (Tgt 4))
      else
        (PiLp.proj 2 (fun _ : Fin 4 => ℝ) ⟨i.val - 4, by omega⟩).comp
          (ContinuousLinearMap.snd ℝ (Tgt 4) (Tgt 4))))

@[simp] lemma pUpCLM_apply_fst (a b : Tgt 4) (k : Fin 4) :
    pUpCLM (a, b) (Fin.castAdd 4 k) = a k := by
  simp [pUpCLM]

@[simp] lemma pUpCLM_apply_snd (a b : Tgt 4) (k : Fin 4) :
    pUpCLM (a, b) (Fin.natAdd 4 k) = b k := by
  simp [pUpCLM]

@[simp] lemma pUpCLM_apply (a b : Tgt 4) : pUpCLM (a, b) = pUp a b := by
  ext i
  revert i
  refine Fin.addCases (m := 4) (n := 4) (motive := fun i : Fin 8 =>
    pUpCLM (a, b) i = pUp a b i) ?_ ?_
  · intro k
    rw [pUpCLM_apply_fst, Work.Drive.pairUp_apply_fst]
  · intro k
    rw [pUpCLM_apply_snd, Work.Drive.pairUp_apply_snd]

/-- The first block of a vector of `ℝ⁸`. -/
def fst8 (w : Tgt 8) : Tgt 4 := WithLp.toLp 2 fun i : Fin 4 => w (Fin.castAdd 4 i)

/-- The second block of a vector of `ℝ⁸`. -/
def snd8 (w : Tgt 8) : Tgt 4 := WithLp.toLp 2 fun i : Fin 4 => w (Fin.natAdd 4 i)

@[simp] lemma pUp_fst8_snd8 (w : Tgt 8) : pUp (fst8 w) (snd8 w) = w := by
  ext i
  revert i
  refine Fin.addCases (m := 4) (n := 4)
    (motive := fun i : Fin 8 => pUp (fst8 w) (snd8 w) i = w i) ?_ ?_
  · intro k; simp [fst8, Work.Drive.pairUp_apply_fst]
  · intro k; simp [snd8, Work.Drive.pairUp_apply_snd]

@[simp] lemma pUp_eq_zero_iff (a b : Tgt 4) : pUp a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext k
      have hh := congrFun (congrArg (fun z : Tgt 8 => z.ofLp) h) (Fin.castAdd 4 k)
      simpa [pUp, Work.Drive.pairUp_apply_fst] using hh
    · ext k
      have hh := congrFun (congrArg (fun z : Tgt 8 => z.ofLp) h) (Fin.natAdd 4 k)
      simpa [pUp, Work.Drive.pairUp_apply_snd] using hh
  · rintro ⟨rfl, rfl⟩
    ext i
    revert i
    refine Fin.addCases (m := 4) (n := 4) (motive := fun i : Fin 8 =>
      pUp 0 0 i = (0 : Tgt 8) i) ?_ ?_
    · intro k; simp [pUp, Work.Drive.pairUp_apply_fst]
    · intro k; simp [pUp, Work.Drive.pairUp_apply_snd]

lemma pUp_injective : Function.Injective (fun z : Tgt 4 × Tgt 4 => pUp z.1 z.2) := by
  intro z z' h
  have h1 : pUp z.1 z.2 = pUp z'.1 z'.2 := h
  refine Prod.ext ?_ ?_
  · ext k
    have hh := congrFun (congrArg (fun w : Tgt 8 => w.ofLp) h1) (Fin.castAdd 4 k)
    simpa [pUp, Work.Drive.pairUp_apply_fst] using hh
  · ext k
    have hh := congrFun (congrArg (fun w : Tgt 8 => w.ofLp) h1) (Fin.natAdd 4 k)
    simpa [pUp, Work.Drive.pairUp_apply_snd] using hh

/-- Componentwise derivative of a stacked pair. -/
theorem hasFDerivAt_pUp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E → Tgt 4} {A' B' : E →L[ℝ] Tgt 4} {x : E}
    (hA : HasFDerivAt A A' x) (hB : HasFDerivAt B B' x) :
    HasFDerivAt (fun y => pUp (A y) (B y)) (pUpCLM.comp (A'.prod B')) x := by
  have h : HasFDerivAt (fun y => (A y, B y)) (A'.prod B') x := hA.prodMk hB
  have h2 := (pUpCLM.hasFDerivAt (x := (A x, B x))).comp x h
  simpa [Function.comp_def] using h2

/-- The derivative of a stacked pair, pointwise. -/
theorem fderiv_pUp_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E → Tgt 4} {A' B' : E →L[ℝ] Tgt 4} {x : E}
    (hA : HasFDerivAt A A' x) (hB : HasFDerivAt B B' x) (v : E) :
    fderiv ℝ (fun y => pUp (A y) (B y)) x v = pUp (A' v) (B' v) := by
  rw [(hasFDerivAt_pUp hA hB).fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, pUpCLM_apply]

/-! ## The three blocks of the nine-box -/

/-- The `k`-th block projection of the nine-box, as a continuous linear map. -/
def bPartC (k : Fin 3) : Amb 8 →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
    (ContinuousLinearMap.pi (fun j : Fin 3 =>
      PiLp.proj 2 (fun _ : Fin 9 => ℝ) (Work.Drive.bIdx k j)))

lemma bPartC_apply (k : Fin 3) (x : Amb 8) (j : Fin 3) : bPartC k x j = x (Work.Drive.bIdx k j) := by
  simp [bPartC, PiLp.proj_apply]

@[simp] lemma bPartC_eq_bPart (k : Fin 3) (x : Amb 8) : bPartC k x = Work.Drive.bPart k x := by
  ext j
  rw [bPartC_apply, Work.Drive.bPart_apply]

/-- The point of the nine-box whose three blocks are prescribed. -/
def mk3 (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) : Amb 8 :=
  WithLp.toLp 2 (fun i : Fin 9 => v ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩)

lemma mk3_bIdx (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) (k j : Fin 3) :
    mk3 v (Work.Drive.bIdx k j) = v k j := by
  have h1 : ((Work.Drive.bIdx k j).val / 3) = k.val := by
    rw [Work.Drive.bIdx_val]; omega
  have h2 : ((Work.Drive.bIdx k j).val % 3) = j.val := by
    rw [Work.Drive.bIdx_val]; omega
  show (WithLp.toLp 2 (fun i : Fin 9 => v ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩) :
    EuclideanSpace ℝ (Fin 9)) _ = _
  simp only [WithLp.ofLp_toLp, h1, h2]

@[simp] lemma bPartC_mk3 (k : Fin 3) (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    bPartC k (mk3 v) = v k := by
  ext j
  rw [bPartC_apply, mk3_bIdx]

/-- The identification of the nine-box coordinates with the three-cube picture. -/
def tripleEquiv : Amb 8 ≃ (Fin 3 → EuclideanSpace ℝ (Fin 3)) where
  toFun x := fun k => Work.Drive.bPart k x
  invFun v := mk3 v
  left_inv x := by
    ext i
    obtain ⟨k, j, hk⟩ : ∃ (k j : Fin 3), Work.Drive.bIdx k j = i :=
      ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩, by
        ext
        rw [Work.Drive.bIdx_val]
        have h := Nat.mod_add_div i.val 3
        omega⟩
    rw [← hk, mk3_bIdx, Work.Drive.bPart_apply]
  right_inv v := by
    funext k
    change Work.Drive.bPart k (mk3 v) = v k
    rw [← bPartC_eq_bPart k (mk3 v)]
    exact bPartC_mk3 k v

@[simp] lemma tripleEquiv_apply (x : Amb 8) (k : Fin 3) :
    tripleEquiv x k = Work.Drive.bPart k x := rfl

@[simp] lemma tripleEquiv_symm_apply (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) {k j : Fin 3} :
    (tripleEquiv.symm v) (Work.Drive.bIdx k j) = v k j := mk3_bIdx v k j

/-! ## The triple intersection set -/

/-- The three chains meet at `x`. -/
def meet3 (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (x : Amb 8) : Prop :=
  D 0 (bPartC 0 x) = D 1 (bPartC 1 x) ∧ D 0 (bPartC 0 x) = D 2 (bPartC 2 x)

/-- The triple intersection set in the nine-box. -/
def K3 (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) : Set (Amb 8) :=
  {x | x ∈ Submission.Drive.unitBox 8 ∧ meet3 D x}

/-- The triple intersection set on the boundary of the nine-box. -/
def bK3 (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) : Set (Amb 8) :=
  {x | x ∈ Submission.Drive.unitBox 8 ∧ meet3 D x ∧ x ∈ Submission.Drive.unitBoxBdry 8}

/-- The part of the triple intersection set whose `k`-th block is on a face of the nine-box. -/
def S3 (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) : Set (Amb 8) :=
  {x | x ∈ Submission.Drive.unitBox 8 ∧ meet3 D x ∧ Work.Drive.onBlockFace k x}

@[simp] lemma mem_K3 {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} {x : Amb 8} :
    x ∈ K3 D ↔ x ∈ Submission.Drive.unitBox 8 ∧ meet3 D x := Iff.rfl

@[simp] lemma mem_bK3 {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} {x : Amb 8} :
    x ∈ bK3 D ↔ x ∈ Submission.Drive.unitBox 8 ∧ meet3 D x ∧
      x ∈ Submission.Drive.unitBoxBdry 8 := Iff.rfl

@[simp] lemma mem_S3 {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} {k : Fin 3} {x : Amb 8} :
    x ∈ S3 D k ↔ x ∈ Submission.Drive.unitBox 8 ∧ meet3 D x ∧ Work.Drive.onBlockFace k x :=
  Iff.rfl

@[simp] lemma meet3_iff_tripleEquiv {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} {x : Amb 8} :
    meet3 D x ↔ D 0 (tripleEquiv x 0) = D 1 (tripleEquiv x 1) ∧
      D 0 (tripleEquiv x 0) = D 2 (tripleEquiv x 2) := by
  simp only [meet3, tripleEquiv_apply, bPartC_eq_bPart]

/-- Membership in the nine-box, blockwise. -/
theorem mem_unitBox8_iff (x : Amb 8) :
    x ∈ Submission.Drive.unitBox 8 ↔ ∀ k : Fin 3, Work.Drive.bPart k x ∈ Submission.Drive.unitBox 2 := by
  constructor
  · intro hx k j
    rw [Work.Drive.bPart_apply]
    exact hx (Work.Drive.bIdx k j)
  · intro hx i
    obtain ⟨k, j, hk⟩ : ∃ (k j : Fin 3), Work.Drive.bIdx k j = i :=
      ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩, by
        ext
        rw [Work.Drive.bIdx_val]
        have h := Nat.mod_add_div i.val 3
        omega⟩
    rw [← hk, ← Work.Drive.bPart_apply]
    exact hx k j

/-- A block is on a face of the nine-box iff that block is on the boundary of its cube. -/
theorem onBlockFace_iff_of_mem (x : Amb 8) (hx : x ∈ Submission.Drive.unitBox 8) (k : Fin 3) :
    Work.Drive.onBlockFace k x ↔ Work.Drive.bPart k x ∈ Submission.Drive.unitBoxBdry 2 := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨(mem_unitBox8_iff x).mp hx k, j, hj⟩
  · rintro ⟨-, j, hj⟩
    exact ⟨j, hj⟩

/-- Membership in the boundary of the nine-box, blockwise. -/
theorem mem_unitBoxBdry8_iff (x : Amb 8) :
    x ∈ Submission.Drive.unitBoxBdry 8 ↔ x ∈ Submission.Drive.unitBox 8 ∧
      ∃ k : Fin 3, Work.Drive.bPart k x ∈ Submission.Drive.unitBoxBdry 2 := by
  rw [Work.Drive.mem_unitBoxBdry_nine_iff]
  constructor
  · rintro ⟨hx, h | h | h⟩
    · exact ⟨hx, 0, (onBlockFace_iff_of_mem x hx 0).mp h⟩
    · exact ⟨hx, 1, (onBlockFace_iff_of_mem x hx 1).mp h⟩
    · exact ⟨hx, 2, (onBlockFace_iff_of_mem x hx 2).mp h⟩
  · rintro ⟨hx, k, hk⟩
    refine ⟨hx, ?_⟩
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with h | h | h
    · subst h; exact Or.inl ((onBlockFace_iff_of_mem x hx 0).mpr hk)
    · subst h; exact Or.inr (Or.inl ((onBlockFace_iff_of_mem x hx 1).mpr hk))
    · subst h; exact Or.inr (Or.inr ((onBlockFace_iff_of_mem x hx 2).mpr hk))

/-- The boundary part of the triple intersection set is the union of the three face parts. -/
theorem bK3_eq_union (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) :
    bK3 D = S3 D 0 ∪ S3 D 1 ∪ S3 D 2 := by
  ext x
  simp only [Set.mem_union, mem_S3, mem_bK3]
  constructor
  · rintro ⟨hbox, hmeet, hbdry⟩
    obtain ⟨-, k, hk⟩ := (mem_unitBoxBdry8_iff x).mp hbdry
    have hface : Work.Drive.onBlockFace k x := (onBlockFace_iff_of_mem x hbox k).mpr hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with h | h | h
    · subst h; exact Or.inl (Or.inl ⟨hbox, hmeet, hface⟩)
    · subst h; exact Or.inl (Or.inr ⟨hbox, hmeet, hface⟩)
    · subst h; exact Or.inr ⟨hbox, hmeet, hface⟩
  · rintro ((⟨hbox, hmeet, hf⟩ | ⟨hbox, hmeet, hf⟩) | ⟨hbox, hmeet, hf⟩)
    · exact ⟨hbox, hmeet, (mem_unitBoxBdry8_iff x).mpr
        ⟨hbox, 0, (onBlockFace_iff_of_mem x hbox 0).mp hf⟩⟩
    · exact ⟨hbox, hmeet, (mem_unitBoxBdry8_iff x).mpr
        ⟨hbox, 1, (onBlockFace_iff_of_mem x hbox 1).mp hf⟩⟩
    · exact ⟨hbox, hmeet, (mem_unitBoxBdry8_iff x).mpr
        ⟨hbox, 2, (onBlockFace_iff_of_mem x hbox 2).mp hf⟩⟩

/-- The three face parts, transported to the three-cube picture. -/
theorem S3_eq_preimage (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    S3 D k = tripleEquiv ⁻¹' (Work.Drive.tripleBdryMeet M D k) := by
  ext x
  simp only [mem_S3, Work.Drive.tripleBdryMeet, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨hbox, hmeet, hf⟩
    exact ⟨(mem_unitBox8_iff x).mp hbox, hmeet.1, hmeet.2,
      (onBlockFace_iff_of_mem x hbox k).mp hf⟩
  · rintro ⟨hbox, h1, h2, hf⟩
    exact ⟨(mem_unitBox8_iff x).mpr hbox, ⟨h1, h2⟩,
      (onBlockFace_iff_of_mem x ((mem_unitBox8_iff x).mpr hbox) k).mpr hf⟩

/-! ## The chart region and the charted difference map -/

/-- The region of the chart at `p` on which all three chains take their values in its source. -/
def region3 (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) : Set (Amb 8) :=
  {x | ∀ k, D k (bPartC k x) ∈ (Work.Drive.chr p).source}

/-- The charted difference map of the three chains: its first block is
`φ (D₀ x₀) − φ (D₁ x₁)` and its second block `φ (D₀ x₀) − φ (D₂ x₂)`. -/
def chartDiff3 (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) : Amb 8 → Tgt 8 :=
  fun x => pUp ((Work.Drive.chr p) (D 0 (bPartC 0 x)) - (Work.Drive.chr p) (D 1 (bPartC 1 x)))
    ((Work.Drive.chr p) (D 0 (bPartC 0 x)) - (Work.Drive.chr p) (D 2 (bPartC 2 x)))

lemma mem_region3 {p : M} {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} {x : Amb 8} :
    x ∈ region3 p D ↔ ∀ k, D k (bPartC k x) ∈ (Work.Drive.chr p).source := Iff.rfl

/-- The charted difference map vanishes exactly at the triple intersections. -/
theorem chartDiff3_eq_zero_iff {p : M} {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} {x : Amb 8}
    (hx : x ∈ region3 p D) :
    chartDiff3 p D x = 0 ↔ meet3 D x := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have key : chartDiff3 p D x = 0 ↔
      ((Work.Drive.chr p) (D 0 (bPartC 0 x)) = (Work.Drive.chr p) (D 1 (bPartC 1 x)) ∧
      (Work.Drive.chr p) (D 0 (bPartC 0 x)) = (Work.Drive.chr p) (D 2 (bPartC 2 x))) := by
    simp only [chartDiff3, pUp_eq_zero_iff, sub_eq_zero]
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := key.mp h
    exact ⟨(Work.Drive.chr p).injOn h0 h1 ha, (Work.Drive.chr p).injOn h0 h2 hb⟩
  · rintro ⟨ha, hb⟩
    exact key.mpr ⟨by rw [ha], by rw [hb]⟩

theorem isOpen_region3 (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, Continuous (D k)) : IsOpen (region3 p D) := by
  have h : region3 p D = ⋂ k : Fin 3, {x : Amb 8 | D k (bPartC k x) ∈ (Work.Drive.chr p).source} := by
    ext x; simp [region3]
  rw [h]
  exact isOpen_iInter_of_finite fun k =>
    ((hD k).comp (bPartC k).continuous).isOpen_preimage _
      (Work.Drive.chr p).open_source

/-- At a triple intersection point whose image lies in the chart at that point, that chart
contains all three images. -/
theorem mem_region3_self (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) {x : Amb 8}
    (hm : meet3 D x) : x ∈ region3 (D 0 (bPartC 0 x)) D := by
  intro k
  have hmem : ∀ y : M, y ∈ (Work.Drive.chr y).source := fun y => by
    rw [Work.Drive.chr, ← extChartAt_source (I := 𝓡 4) y]
    exact mem_extChartAt_source _
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with h | h | h <;> rw [h]
  · exact hmem _
  · rw [← hm.1]; exact hmem _
  · rw [← hm.2]; exact hmem _

/-! ## The chart-independent tangent map -/

/-- The derivative `mfderiv D k (bPart k x)`, as a continuous linear map into `ℝ⁴`. -/
def md3 (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) (x : Amb 8) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] Tgt 4 :=
  show EuclideanSpace ℝ (Fin 3) →L[ℝ] Tgt 4 from mfderiv (𝓡 3) (𝓡 4) (D k) (bPartC k x)

/-- The change of coordinates from the chart at the point itself to the chart at `p`, at the
`k`-th image point. -/
def tc (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) (x : Amb 8) :
    Tgt 4 →L[ℝ] Tgt 4 :=
  tangentCoordChange (𝓡 4) (D k (bPartC k x)) p (D k (bPartC k x))

/-- The chart-independent part of the derivative of the charted difference map: the pair
`(d₀v₀ − d₁v₁, d₀v₀ − d₂v₂)` read in the coordinates of the chart at `p`. -/
def tan3 (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (x : Amb 8) :
    Amb 8 →L[ℝ] (Tgt 4 × Tgt 4) :=
  (((tc p D 0 x).comp (md3 D 0 x)).comp (bPartC 0) -
      ((tc p D 1 x).comp (md3 D 1 x)).comp (bPartC 1)).prod
    (((tc p D 0 x).comp (md3 D 0 x)).comp (bPartC 0) -
      ((tc p D 2 x).comp (md3 D 2 x)).comp (bPartC 2))

theorem tan3_apply (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (x v : Amb 8) :
    tan3 p D x v =
      (tangentCoordChange (𝓡 4) (D 0 (bPartC 0 x)) p (D 0 (bPartC 0 x))
          (mfderiv (𝓡 3) (𝓡 4) (D 0) (bPartC 0 x) (bPartC 0 v)) -
        tangentCoordChange (𝓡 4) (D 1 (bPartC 1 x)) p (D 1 (bPartC 1 x))
          (mfderiv (𝓡 3) (𝓡 4) (D 1) (bPartC 1 x) (bPartC 1 v)),
      tangentCoordChange (𝓡 4) (D 0 (bPartC 0 x)) p (D 0 (bPartC 0 x))
          (mfderiv (𝓡 3) (𝓡 4) (D 0) (bPartC 0 x) (bPartC 0 v)) -
        tangentCoordChange (𝓡 4) (D 2 (bPartC 2 x)) p (D 2 (bPartC 2 x))
          (mfderiv (𝓡 3) (𝓡 4) (D 2) (bPartC 2 x) (bPartC 2 v))) := by
  simp only [tan3, tc, md3, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
  rfl

/-! ## The two hypotheses of the target theorem, in the nine-box picture -/

/-- **Transversality of the three chains**, in the nine-box picture: at every triple intersection
point of the nine-box the three derivatives are transverse. -/
def transHyp (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) : Prop :=
  ∀ x : Amb 8, x ∈ Submission.Drive.unitBox 8 → meet3 D x →
    Work.Drive.TripleTransverse (md3 D 0 x) (md3 D 1 x) (md3 D 2 x)

/-- **The face hypothesis**, in the nine-box picture: at every triple intersection point on the
boundary of the nine-box, exactly one coordinate of exactly one block is on a face, everything else
is strictly inside, and the triple intersection crosses that face transversally (there is a common
direction whose corresponding coordinate is non-zero). -/
def faceHyp (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) : Prop :=
  ∀ x : Amb 8, x ∈ Submission.Drive.unitBox 8 → meet3 D x →
    x ∈ Submission.Drive.unitBoxBdry 8 →
    ∃ (k : Fin 3) (i : Fin 3),
      (x (Work.Drive.bIdx k i) = 0 ∨ x (Work.Drive.bIdx k i) = 1) ∧
      (∀ j : Fin 3, j ≠ i → x (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
      ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
        Work.Drive.TripleCommonDir (md3 D 0 x) (md3 D 1 x) (md3 D 2 x) v ∧ v k i ≠ 0

/-! ## Hypotheses on a field along the triple intersection set -/

/-- `V` is non-zero on the triple intersection set. -/
def Vne (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (V : Amb 8 → Amb 8) : Prop :=
  ∀ x : Amb 8, x ∈ K3 D → V x ≠ 0

/-- `V` is tangent to the triple intersection set: it is killed by the derivative of every charted
difference map at every triple intersection point. -/
def Vtan (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (V : Amb 8 → Amb 8) : Prop :=
  ∀ x : Amb 8, x ∈ K3 D → ∀ p : M, x ∈ region3 p D →
    fderiv ℝ (chartDiff3 p D) x (V x) = 0

/-- The face condition for a field `V` along the triple intersection set: at every boundary triple
intersection the field crosses the face of the box transversally. -/
def Vface (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (V : Amb 8 → Amb 8) : Prop :=
  ∀ b : Amb 8, b ∈ K3 D → b ∈ Submission.Drive.unitBoxBdry 8 →
    ∃ i : Fin 9, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 9, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
      V b i ≠ 0

end

end Work.Drive.TParity

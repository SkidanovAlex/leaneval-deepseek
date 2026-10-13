import Mathlib
import Submission.Work.WilG4a.CD.fibDerivDefs
import Submission.Work.WilG4a.CD.fibDerivAux
import Submission.Work.WilG4a.CD.punctured_contDiffAt

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology ContDiff

namespace Work.WilG4a.CD
open WilkiesDesign WilkiesConjecture Work.WilG4a

/-! ## Pointwise ingredients

The five lemmas below are the pointwise content of the equivalence.  The `⇒`-direction
components are `mem_fibValC_aux` (the fibre value tends to `f l x`) and `mem_fibLimSet_aux`
(the `m`-th slice derivative is the limit of the joint `∂_x^m` along the fibre); the
`⇐`-direction components are `exists_delta_aux` (the value limit is `f l x`),
`exists_limit_aux` (the limits of the first `j` joint `x`-derivatives exist) and
`tendsto_aux` (the limit of the joint `∂_x^j` is the value coordinate).  All of them rest on
the currying identity `iteratedDeriv_eq_jointDeriv` of `fibDerivAux`, which identifies the
`m`-th derivative of the slice with the joint `∂_x^m` on the joint `C^m` locus. -/

/-- **`⇒`, value component.**  If the slice is `C^j` at `x` then the fibre value set of `f` at
`(l,x)` contains the point `f l x`: the `graphFam`-values along the punctured fibre tend to
`f l x`. -/
private theorem mem_fibValC_aux {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) {j : ℕ}
    (l : Fin p → ℝ) (x : ℝ) (h : ContDiffAt ℝ j (fun t : ℝ => f l t) x) :
    Fin.snoc l x ∈ fibValC f := by
  have hc : ContinuousAt (fun t : ℝ => f l t) x := h.continuousAt
  change ∃ y : ℝ, Fin.snoc (Fin.snoc l x) y ∈ fibValLim f ∩ graphFam f
  refine ⟨f l x, ?_, (mem_graphFam_iff f l x (f l x)).mpr rfl⟩
  simp only [fibValLim, fibLimitSet, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
  intro ε hε
  obtain ⟨δ, hδ, hδp⟩ := exists_delta_of_continuousAt hc ε hε
  refine ⟨δ, hδ, fun t ht hlt v hmem => ?_⟩
  simp only [mem_graphFam_iff] at hmem
  rw [hmem]
  exact le_of_lt (hδp t ht hlt)

/-- **`⇒`, derivative-limit component.**  On the fibre germ, the `m`-th slice derivative at `x`
(`m ≤ j`) is the limit of the joint `∂_x^m` along the punctured fibre: the joint `∂_x^m` agrees
with the slice derivative on the (germ) punctured neighbourhood, where the joint function is
`C^m`, and it is continuous at `x` because the slice is `C^j` there. -/
private theorem mem_fibLimSet_aux {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) {j m : ℕ} (hmj : m ≤ j)
    (l : Fin p → ℝ) (x : ℝ) (hΓ : Fin.snoc l x ∈ fibGerm f j)
    (h : ContDiffAt ℝ j (fun t : ℝ => f l t) x) :
    Fin.snoc (Fin.snoc l x) (iteratedDeriv m (fun t : ℝ => f l t) x) ∈ fibLimSet f m := by
  obtain ⟨ρ, hρ, hsm⟩ := smoothLocus_of_fibGerm f j hΓ
  have hcm : ContDiffAt ℝ m (fun t : ℝ => f l t) x :=
    h.of_le (show ((m : ℕ∞ω) ≤ (j : ℕ∞ω)) from by exact_mod_cast hmj)
  have hc : ContinuousAt (iteratedDeriv m (fun t : ℝ => f l t)) x :=
    continuousAt_iteratedDeriv_of_contDiffAt hcm
  rw [fibLimSet, mem_fibLimSet]
  simp only [Fin.init_snoc, Fin.snoc_last]
  intro ε hε
  obtain ⟨δ, hδ, hδp⟩ := exists_delta_of_continuousAt hc ε hε
  refine ⟨min δ ρ, lt_min hδ hρ, fun t ht hlt v hmem => ?_⟩
  have htδ : |t - x| < δ := lt_of_lt_of_le hlt (min_le_left _ _)
  have htρ : |t - x| < ρ := lt_of_lt_of_le hlt (min_le_right _ _)
  have hsmj : Fin.snoc l t ∈ smoothLocus f j := hsm t ht htρ
  have hv : v = iteratedDeriv m (fun s : ℝ => f l s) t := by
    have hv0 : v = jointDeriv f m l t := ((mem_derivGraphSet_iff f m l t v).mp hmem).2
    rw [hv0]
    exact (iteratedDeriv_eq_jointDeriv f m l t
      (contDiffAt_famFun_of_smooth f hmj hsmj)).symm
  rw [hv]
  exact le_of_lt (hδp t ht htδ)

/-- **`⇐`, value-limit component.**  The fibre value set of `f` at `(l,x)` pins the value at
`f l x`: along the punctured fibre the `graphFam`-values tend to `f l x`. -/
private theorem exists_delta_aux {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ)
    (l : Fin p → ℝ) (x : ℝ) (h : Fin.snoc l x ∈ fibValC f) :
    ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, t ≠ x → |t - x| < δ → |f l t - f l x| < ε := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨hlim, hgr⟩ := hy
  have hyx : y = f l x := (mem_graphFam_iff f l x y).mp hgr
  simp only [fibValLim, mem_fibLimSet, Fin.init_snoc, Fin.snoc_last] at hlim
  intro ε hε
  obtain ⟨δ, hδ, hδp⟩ := hlim (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun t ht hlt => ?_⟩
  have hb := hδp t ht hlt (f l t) ((mem_graphFam_iff f l t (f l t)).mpr rfl)
  rw [hyx] at hb
  linarith

/-- **`⇐`, existence of the limits of the lower joint `x`-derivatives.**  A projected limit along
the fibre over `(l,x)` is the limit of the corresponding slice derivative at the punctured
point: on the germ the joint `∂_x^m` is the slice derivative and its values along the fibre are
the ones the fibre limit set controls. -/
private theorem exists_limit_aux {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) {j m : ℕ} (hmj : m ≤ j)
    (l : Fin p → ℝ) (x : ℝ) (hΓ : Fin.snoc l x ∈ fibGerm f j)
    (h : Fin.snoc l x ∈ projLast (fibLimSet f m)) :
    ∃ L : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, t ≠ x → |t - x| < δ →
      |iteratedDeriv m (fun s : ℝ => f l s) t - L| < ε := by
  obtain ⟨ρ, hρ, hsm⟩ := smoothLocus_of_fibGerm f j hΓ
  obtain ⟨y, hy⟩ := h
  refine ⟨y, fun ε hε => ?_⟩
  simp only [fibLimSet, mem_fibLimSet, Fin.init_snoc, Fin.snoc_last] at hy
  obtain ⟨δ, hδ, hδp⟩ := hy (ε / 2) (by linarith)
  refine ⟨min δ ρ, lt_min hδ hρ, fun t ht hlt => ?_⟩
  have htδ : |t - x| < δ := lt_of_lt_of_le hlt (min_le_left _ _)
  have htρ : |t - x| < ρ := lt_of_lt_of_le hlt (min_le_right _ _)
  have hsmj : Fin.snoc l t ∈ smoothLocus f j := hsm t ht htρ
  have hsmn : Fin.snoc l t ∈ smoothLocus f m := smoothLocus_subset f hmj hsmj
  have hkey : iteratedDeriv m (fun s : ℝ => f l s) t = jointDeriv f m l t :=
    iteratedDeriv_eq_jointDeriv f m l t (contDiffAt_famFun_of_smooth f hmj hsmj)
  have hmem : Fin.snoc (Fin.snoc l t) (iteratedDeriv m (fun s : ℝ => f l s) t) ∈
      derivGraphSet f m :=
    (mem_derivGraphSet_iff f m l t (iteratedDeriv m (fun s : ℝ => f l s) t)).mpr
      ⟨hsmn, hkey⟩
  have hb := hδp t ht htδ (iteratedDeriv m (fun s : ℝ => f l s) t) hmem
  linarith

/-- **`⇐`, top-derivative limit component.**  The limit of the joint `∂_x^j` along the fibre is
the value coordinate `y`, which together with `C^j`-ness of the slice identifies `y` with the
`j`-th slice derivative. -/
private theorem tendsto_aux {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) {j : ℕ}
    (l : Fin p → ℝ) (x y : ℝ) (hΓ : Fin.snoc l x ∈ fibGerm f j)
    (h : Fin.snoc (Fin.snoc l x) y ∈ fibLimSet f j) :
    ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, t ≠ x → |t - x| < δ →
      |iteratedDeriv j (fun s : ℝ => f l s) t - y| < ε := by
  intro ε hε
  obtain ⟨ρ, hρ, hsm⟩ := smoothLocus_of_fibGerm f j hΓ
  simp only [fibLimSet, mem_fibLimSet, Fin.init_snoc, Fin.snoc_last] at h
  obtain ⟨δ, hδ, hδp⟩ := h (ε / 2) (by linarith)
  refine ⟨min δ ρ, lt_min hδ hρ, fun t ht hlt => ?_⟩
  have htδ : |t - x| < δ := lt_of_lt_of_le hlt (min_le_left _ _)
  have htρ : |t - x| < ρ := lt_of_lt_of_le hlt (min_le_right _ _)
  have hsmooth : Fin.snoc l t ∈ smoothLocus f j := hsm t ht htρ
  have hkey : iteratedDeriv j (fun s : ℝ => f l s) t = jointDeriv f j l t :=
    iteratedDeriv_eq_jointDeriv f j l t (contDiffAt_famFun_of_smooth f le_rfl hsmooth)
  have hmem : Fin.snoc (Fin.snoc l t) (jointDeriv f j l t) ∈ derivGraphSet f j :=
    (mem_derivGraphSet_iff f j l t (jointDeriv f j l t)).mpr ⟨hsmooth, rfl⟩
  have hb := hδp t ht htδ (jointDeriv f j l t) hmem
  rw [hkey]
  linarith

/-- On the fibre-germ set `Γ = fibGerm f j`, the target set `T_j(f) = fibDerivSet f j` coincides with the `Ω`-approximation `R = fibMainSet f j`: a `j`-times continuously differentiable slice is exactly one whose punctured fibre neighbourhood is jointly `C^j` and whose value and first `j` joint `x`-derivatives along the fibre have limits. The direction `⇒` uses that on `Γ` the punctured fibre neighbourhood lies in `smoothLocus f j`, where the slice's `m`-th derivative equals the joint `∂_x^m` (a currying identity for `iteratedFDeriv` along the affine slice `t ↦ Fin.snoc l t`); the direction `⇐` feeds those limits into `Work.WilG4a.CD.punctured_contDiffAt`. -/
theorem fibDerivSet_eq_fibMainSet_on_germ (p : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) :
    ∀ w : Fin (p + 2) → ℝ, Fin.init w ∈ Work.WilG4a.CD.fibGerm f j →
      (w ∈ Work.WilG4a.CD.fibDerivSet f j ↔ w ∈ Work.WilG4a.CD.fibMainSet f j) := by
  -- The `⇒` direction, in the coordinates `w = (l, x, y)` of a `Fin.snoc`.
  have hfwd : ∀ (l : Fin p → ℝ) (x y : ℝ), Fin.snoc l x ∈ fibGerm f j →
      (ContDiffAt ℝ j (fun t : ℝ => f l t) x ∧
        y = iteratedDeriv j (fun t : ℝ => f l t) x) →
      Fin.snoc l x ∈ fibGerm f j ∧ Fin.snoc l x ∈ fibValC f ∧
        Fin.snoc (Fin.snoc l x) y ∈ fibLimSet f j ∧
        (∀ m ∈ Finset.Icc 1 j, Fin.snoc l x ∈ projLast (fibLimSet f m)) := by
    intro l x y hΓ hT
    refine ⟨hΓ, mem_fibValC_aux f l x hT.1, ?_, ?_⟩
    · rw [hT.2]
      exact mem_fibLimSet_aux f (j := j) (m := j) le_rfl l x hΓ hT.1
    · intro m hm
      rw [Finset.mem_Icc] at hm
      exact ⟨iteratedDeriv m (fun t : ℝ => f l t) x,
        mem_fibLimSet_aux f (j := j) (m := m) hm.2 l x hΓ hT.1⟩
  -- The `⇐` direction, in the same coordinates.
  have hbwd : ∀ (l : Fin p → ℝ) (x y : ℝ), Fin.snoc l x ∈ fibGerm f j →
      (Fin.snoc l x ∈ fibGerm f j ∧ Fin.snoc l x ∈ fibValC f ∧
        Fin.snoc (Fin.snoc l x) y ∈ fibLimSet f j ∧
        (∀ m ∈ Finset.Icc 1 j, Fin.snoc l x ∈ projLast (fibLimSet f m))) →
      ContDiffAt ℝ j (fun t : ℝ => f l t) x ∧
        y = iteratedDeriv j (fun t : ℝ => f l t) x := by
    intro l x y hΓ hR
    obtain ⟨-, hvalC, hlimJ, hlimM⟩ := hR
    obtain ⟨ρ, hρ, hslice⟩ := sliceContDiffAt_of_germ f j hΓ
    have hcd : ContDiffAt ℝ j (fun t : ℝ => f l t) x := by
      refine punctured_contDiffAt (fun t : ℝ => f l t) x j ρ hρ ?_ ?_ ?_
      · intro t ht htne
        rw [Set.mem_Ioo] at ht
        exact hslice t htne (by rw [abs_lt]; exact ⟨by linarith, by linarith⟩)
      · intro ε hε
        obtain ⟨δ, hδ, hδp⟩ := exists_delta_aux f l x hvalC ε hε
        exact ⟨min δ ρ, lt_min hδ hρ, min_le_right _ _,
          fun t ht hlt => hδp t ht (lt_of_lt_of_le hlt (min_le_left _ _))⟩
      · intro m hm1 hmj
        obtain ⟨L, hL⟩ := exists_limit_aux f (j := j) (m := m) hmj l x hΓ
          (hlimM m (Finset.mem_Icc.mpr ⟨hm1, hmj⟩))
        refine ⟨L, fun ε hε => ?_⟩
        obtain ⟨δ, hδ, hδp⟩ := hL ε hε
        exact ⟨min δ ρ, lt_min hδ hρ, min_le_right _ _, fun t ht hlt =>
          hδp t ht (lt_of_lt_of_le hlt (min_le_left _ _))⟩
    refine ⟨hcd, ?_⟩
    exact (eq_of_tendsto_iteratedDeriv hcd (fun ε hε =>
      tendsto_aux f l x y hΓ hlimJ ε hε)).symm
  intro w hΓw
  -- Read `w` as `Fin.snoc (Fin.snoc l x) y` and the germ membership accordingly.
  have hΓ' : Fin.snoc (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last p)) ∈ fibGerm f j := by
    rw [Fin.snoc_init_self (Fin.init w)]
    exact hΓw
  have hwsnoc : Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last p)))
      (w (Fin.last (p + 1))) = w := by
    rw [Fin.snoc_init_self (Fin.init w)]
    exact Fin.snoc_init_self w
  rw [mem_fibDerivSet, mem_fibMainSet]
  rw [← hwsnoc]
  simp only [Fin.init_snoc, Fin.snoc_last]
  constructor
  · intro hT
    exact hfwd (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last p)) (w (Fin.last (p + 1))) hΓ' hT
  · intro hR
    exact hbwd (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last p)) (w (Fin.last (p + 1))) hΓ' hR

end Work.WilG4a.CD

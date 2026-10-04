import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.evolX.atomZf_pair
import Submission.Work.Diff.EXT.evolX.atomZf_smooth
import Submission.Work.Diff.EXT.evolX.atomSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

namespace Work.Diff.EXT.evolX

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The orthonormality hypothesis of the statement

The statement as requested carries the hypothesis name `OnFrameAtPlaceholder`; it is the orthonormality
of the frame field `W` at the point `x`, i.e. the predicate `ONFrameAt` of `ladderAtoms.lean`.  We
provide it here as an abbreviation so that the requested statement elaborates verbatim. -/
abbrev OnFrameAtPlaceholder (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)) : Prop :=
  ONFrameAt (I := I) (M := M) g x W

/-! ## Helper lemmas

The two `atomStep_*` lemmas are the tuple identities that let the corrections of the outer tower
recursion be identified with the corrections coming from the two tuple positions of the atom; the
others are the smoothness/linearity bookkeeping of a finite sum inserted in one slot of the tower. -/

/-- The `κ`-case of the atom step: inserting the updated tuple at a `κ`-position commutes with the
`if j = s then (curvature vector) else ·` pattern of the atom. -/
theorem atomStep_kappa
    (m l N : ℕ) (s : Fin (m + 4)) (κ : Fin (m + 4) → Fin N) (ξ : Fin (l + 3) → Fin N)
    (hκ : ∀ i j, i ≠ s → j ≠ s → κ i = κ j → i = j)
    (hdisj : ∀ i r, i ≠ s → κ i ≠ ξ r)
    (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (m + 4)) (hi : i ≠ s) (w : Work.Diff.EXT.TField (I := I) (M := M)) :
    (fun j : Fin (m + 4) =>
        if j = s then Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
            (fun r : Fin (l + 3) => Function.update G (κ i) w (ξ r))
        else Function.update G (κ i) w (κ j))
      = Function.update (fun j : Fin (m + 4) => if j = s then
            Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
              (fun r : Fin (l + 3) => G (ξ r)) else G (κ j)) i w := by
  have hZ : (fun r : Fin (l + 3) => Function.update G (κ i) w (ξ r))
      = (fun r : Fin (l + 3) => G (ξ r)) := by
    funext r
    rw [Function.update_apply, if_neg (Ne.symm (hdisj i r hi))]
  rw [hZ]
  funext j
  simp only [Function.update_apply]
  by_cases hjs : j = s
  · have hji' : ¬ (j = i) := fun h => hi (h.symm.trans hjs)
    simp only [if_pos hjs, if_neg hji']
  · rw [if_neg hjs]
    by_cases hji : j = i
    · simp only [if_pos hji, if_neg hjs, if_pos (congrArg κ hji)]
    · have hkj : κ j ≠ κ i := fun h => hji (hκ j i hjs hi h)
      simp only [if_neg hjs, if_neg hji, if_neg hkj]

/-- The `ξ`-case of the atom step: inserting the updated tuple at a `ξ`-position replaces the
curvature-vector slot of the atom. -/
theorem atomStep_xi
    (m l N : ℕ) (s : Fin (m + 4)) (κ : Fin (m + 4) → Fin N) (ξ : Fin (l + 3) → Fin N)
    (hdisj : ∀ i r, i ≠ s → κ i ≠ ξ r) (hξ : Function.Injective ξ)
    (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (r : Fin (l + 3)) (w : Work.Diff.EXT.TField (I := I) (M := M)) :
    (fun j : Fin (m + 4) =>
        if j = s then Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
            (fun r' : Fin (l + 3) => Function.update G (ξ r) w (ξ r'))
        else Function.update G (ξ r) w (κ j))
      = Function.update (fun j : Fin (m + 4) => if j = s then
            Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
              (fun r' : Fin (l + 3) => G (ξ r')) else G (κ j)) s
          (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
            (Function.update (fun r' : Fin (l + 3) => G (ξ r')) r w)) := by
  have hcomp : (fun r' : Fin (l + 3) => Function.update G (ξ r) w (ξ r'))
      = Function.update (fun r' : Fin (l + 3) => G (ξ r')) r w := by
    funext r'
    rw [Function.update_apply, Function.update_apply]
    by_cases h : r' = r
    · rw [if_pos h, if_pos (congrArg ξ h)]
    · rw [if_neg h, if_neg (fun hh => h (hξ hh))]
  rw [hcomp]
  funext j
  simp only [Function.update_apply]
  by_cases hjs : j = s
  · simp only [if_pos hjs]
  · have hne : κ j ≠ ξ r := hdisj j r hjs
    simp only [if_neg hjs, if_neg hne]

/-- Smoothness of a finite sum `∑ i ∈ t, c i • Y i` of smooth fields. -/
theorem smoothF_sum_smul {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (Y : ι → Work.Diff.EXT.TField (I := I) (M := M))
    (hY : ∀ i, Work.Diff.EXT.SmoothF (Y i)) :
    Work.Diff.EXT.SmoothF (∑ i ∈ t, c i • Y i) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Work.Diff.GE.cmDiff_zeroField
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact Work.Diff.EXT.smoothF_add
      (Work.Diff.EXT.smoothF_smul (f := fun _ : M => c a)
        (contMDiff_const (c := c a)) (hY a)) ih

/-- Linearity of the tower in one slot with respect to a finite linear combination of fields. -/
theorem ckt_sum_slot {ι : Type*} [Fintype ι] {k : ℕ}
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (F : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ s, Work.Diff.EXT.SmoothF (F s)) (s : Fin (k + 4))
    (c : ι → ℝ) (Y : ι → Work.Diff.EXT.TField (I := I) (M := M))
    (hY : ∀ i, Work.Diff.EXT.SmoothF (Y i)) (z : M) :
    Work.Diff.EXT.ckt g k (Function.update F s (∑ i, c i • Y i)) z
      = ∑ i, c i * Work.Diff.EXT.ckt g k (Function.update F s (Y i)) z := by
  classical
  have hT := Work.Diff.EXT.tensProp_all hLC g k
  have key : ∀ t : Finset ι,
      Work.Diff.EXT.ckt g k (Function.update F s (∑ i ∈ t, c i • Y i)) z
        = ∑ i ∈ t, c i * Work.Diff.EXT.ckt g k (Function.update F s (Y i)) z := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have h0 : (∑ i ∈ (∅ : Finset ι), c i • Y i)
          = (fun _ : M => (0:ℝ)) • (F s) + (fun _ : M => (0:ℝ)) • (F s) := by
        rw [Finset.sum_empty]; funext y; simp
      rw [h0, Finset.sum_empty]
      have hs := congrFun ((hT F hF).2.1 s (F s) (F s) (fun _ : M => (0:ℝ))
        (fun _ : M => (0:ℝ)) (hF s) (hF s)
        (contMDiff_const (c := (0:ℝ))) (contMDiff_const (c := (0:ℝ)))) z
      simpa using hs
    | insert a t ha ih =>
      have hsum : (∑ i ∈ insert a t, c i • Y i)
          = (fun _ : M => c a) • (Y a) + (fun _ : M => (1:ℝ)) • (∑ i ∈ t, c i • Y i) := by
        rw [Finset.sum_insert ha]; funext y; simp
      rw [hsum, Finset.sum_insert ha]
      have hsm : Work.Diff.EXT.SmoothF (∑ i ∈ t, c i • Y i) := smoothF_sum_smul t c Y hY
      have hlin := congrFun ((hT F hF).2.1 s (Y a) (∑ i ∈ t, c i • Y i)
        (fun _ : M => c a) (fun _ : M => (1:ℝ)) (hY a) hsm
        (contMDiff_const (c := c a)) (contMDiff_const (c := (1:ℝ)))) z
      rw [hlin]
      simp only [Pi.add_apply, Pi.mul_apply, smul_eq_mul, one_mul]
      rw [ih]
  simpa using key Finset.univ

/-- **The Leibniz rule for the frame-expanded curvature vector `Zf`** (boundary-free form).

`Zf g W l Ψ = ∑ i, (ckt g l (Fin.snoc Ψ (W i))) • W i` is the level-`l` curvature vector written in
the frame field `W`.  Its covariant derivative along the smooth field `v` is the sum of the
derivatives of its `l + 3` arguments plus the derivative of the level:
`∇_v (Zf l Ψ) = Zf (l+1) (cons v Ψ) + ∑ r, Zf l (update Ψ r (∇_v (Ψ r)))` at `x`. -/
theorem zfLeibnizSelf
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (hON : Work.Diff.EXT.evolX.ONFrameAt (I := I) (M := M) g x W)
    (l : ℕ) (Psi : Fin (l + 3) → Work.Diff.EXT.TField (I := I) (M := M))
    (hPsi : ∀ r, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (Psi r))
    (v : Work.Diff.EXT.TField (I := I) (M := M))
    (hv : Work.Diff.EXT.evolX.SmTf (I := I) (M := M) v) :
    Work.Diff.EXT.dirF (I := I) (M := M) g
        (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) v x
      = Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1) (Fin.cons v Psi) x
        + ∑ r : Fin (l + 3), Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
            (Function.update Psi r (Work.Diff.EXT.dirF (I := I) (M := M) g (Psi r) v)) x := by
  classical
  have hONx : Submission.Diff.IsONFrame g x (fun i => W i x) := hON.self_of_nhds
  have hcongr : ∀ {f hh : M → ℝ}, f =ᶠ[𝓝 x] hh → mvfderiv I f x = mvfderiv I hh x := by
    intro f hh hf
    rw [mvfderiv, mvfderiv, hf.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq hf]
    all_goals first | rfl | (ext w; rfl)
  have hZfsm : Work.Diff.EXT.evolX.SmTf (I := I) (M := M)
      (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) :=
    Work.Diff.EXT.evolX.smTf_Zf (I := I) (M := M) hLC g W hW l Psi hPsi
  have hconsPsi : ∀ r : Fin (l + 1 + 3), Work.Diff.EXT.evolX.SmTf (I := I) (M := M)
      ((Fin.cons v Psi : Fin (l + 1 + 3) → Work.Diff.EXT.TField (I := I) (M := M)) r) := by
    intro r
    induction r using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hv
    | succ r' => rw [Fin.cons_succ]; exact hPsi r'
  have hPsisr : ∀ r : Fin (l + 3), ∀ r' : Fin (l + 3), Work.Diff.EXT.evolX.SmTf (I := I) (M := M)
      ((Function.update Psi r (Work.Diff.EXT.dirF (I := I) (M := M) g (Psi r) v)) r') := by
    intro r r'
    rw [Function.update_apply]
    by_cases h : r' = r
    · rw [if_pos h]
      exact Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g (hPsi r) hv
    · rw [if_neg h]
      exact hPsi r'
  have key : ∀ (D : Work.Diff.EXT.TField (I := I) (M := M)),
      Work.Diff.EXT.evolX.SmTf (I := I) (M := M) D →
      g.inner x (Work.Diff.EXT.dirF (I := I) (M := M) g
          (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) v x) (D x)
        = g.inner x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1) (Fin.cons v Psi) x) (D x)
          + ∑ r : Fin (l + 3), g.inner x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
              (Function.update Psi r (Work.Diff.EXT.dirF (I := I) (M := M) g (Psi r) v)) x) (D x) := by
    intro D hD
    have hfrom : g.inner x (Work.Diff.EXT.dirF (I := I) (M := M) g
          (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) v x) (D x)
        = mvfderiv I (fun y : M => g.inner y
              (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi y) (D y)) x (v x)
          - g.inner x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi x)
              (Work.Diff.EXT.dirF (I := I) (M := M) g D v x) := by
      have hpair := Work.Diff.GE.kato_mvfderiv_inner_lc (I := I) (M := M) g x (v x) hZfsm hD
      rw [hpair]
      rw [show Work.Diff.EXT.dirF (I := I) (M := M) g
            (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) v x
          = Submission.Diff.lcOf g (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) x (v x)
          from rfl]
      rw [show Work.Diff.EXT.dirF (I := I) (M := M) g D v x
          = Submission.Diff.lcOf g D x (v x) from rfl]
      ring
    rw [hfrom]
    have hcong : (fun y : M => g.inner y
          (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi y) (D y))
        =ᶠ[𝓝 x] (fun y : M => Work.Diff.EXT.ckt g l (Fin.snoc Psi D) y) := by
      obtain ⟨s, hs, hsub⟩ := Filter.eventually_iff_exists_mem.mp hON
      obtain ⟨U, hUs, hUopen, hxU⟩ := mem_nhds_iff.mp hs
      refine Filter.eventually_of_mem (hUopen.mem_nhds hxU) (fun y hy => ?_)
      exact Work.Diff.EXT.evolX.atomZf_pair g y W hW
        (Filter.eventually_of_mem (hUopen.mem_nhds hy) (fun z hz => hsub z (hUs hz)))
        l Psi hPsi D hD
    rw [hcongr hcong]
    have hsumid : (∑ s : Fin (l + 4), Work.Diff.EXT.ckt g l
          (Function.update (Fin.snoc Psi D : Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M)) s
            (Work.Diff.EXT.dirF (I := I) (M := M) g
              ((Fin.snoc Psi D : Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M)) s) v)) x)
        = (∑ r : Fin (l + 3), Work.Diff.EXT.ckt g l
            (@Fin.snoc (l + 3) (fun _ => Work.Diff.EXT.TField (I := I) (M := M))
              (Function.update Psi r (Work.Diff.EXT.dirF (I := I) (M := M) g (Psi r) v)) D) x)
          + Work.Diff.EXT.ckt g l
              (@Fin.snoc (l + 3) (fun _ => Work.Diff.EXT.TField (I := I) (M := M))
                Psi (Work.Diff.EXT.dirF (I := I) (M := M) g D v)) x := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      · refine Finset.sum_congr rfl (fun r _ => ?_)
        have htuple : Function.update (Fin.snoc Psi D) r.castSucc
              (Work.Diff.EXT.dirF (I := I) (M := M) g
                ((Fin.snoc Psi D : Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M)) r.castSucc) v)
            = @Fin.snoc (l + 3) (fun _ => Work.Diff.EXT.TField (I := I) (M := M))
                (Function.update Psi r (Work.Diff.EXT.dirF (I := I) (M := M) g (Psi r) v)) D := by
          rw [Fin.snoc_castSucc, ← Fin.snoc_update]
        rw [htuple]
      · have htuple : Function.update (Fin.snoc Psi D) (Fin.last (l + 3))
              (Work.Diff.EXT.dirF (I := I) (M := M) g
                ((Fin.snoc Psi D : Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M))
                  (Fin.last (l + 3))) v)
            = @Fin.snoc (l + 3) (fun _ => Work.Diff.EXT.TField (I := I) (M := M))
                Psi (Work.Diff.EXT.dirF (I := I) (M := M) g D v) := by
          rw [Fin.snoc_last, Fin.update_snoc_last]
        rw [htuple]
    rw [Work.Diff.EXT.mvfderiv_ckt_T2 (I := I) (M := M) g l (Fin.snoc Psi D) v x, hsumid]
    rw [show (Fin.cons v (Fin.snoc Psi D) : Fin (l + 1 + 4) → Work.Diff.EXT.TField (I := I) (M := M))
          = Fin.snoc (Fin.cons v Psi) D from Fin.cons_snoc_eq_snoc_cons v Psi D]
    rw [show Work.Diff.EXT.ckt g (l + 1) (Fin.snoc (Fin.cons v Psi) D) x
          = g.inner x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1) (Fin.cons v Psi) x)
              (D x)
        from (Work.Diff.EXT.evolX.atomZf_pair g x W hW hON (l + 1) (Fin.cons v Psi) hconsPsi D hD).symm]
    rw [show Work.Diff.EXT.ckt g l
          (@Fin.snoc (l + 3) (fun _ => Work.Diff.EXT.TField (I := I) (M := M))
            Psi (Work.Diff.EXT.dirF (I := I) (M := M) g D v)) x
          = g.inner x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi x)
              (Work.Diff.EXT.dirF (I := I) (M := M) g D v x)
        from (Work.Diff.EXT.evolX.atomZf_pair g x W hW hON l Psi hPsi
          (Work.Diff.EXT.dirF (I := I) (M := M) g D v)
          (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g hD hv)).symm]
    rw [Finset.sum_congr rfl (fun r _ =>
      (Work.Diff.EXT.evolX.atomZf_pair g x W hW hON l
        (Function.update Psi r (Work.Diff.EXT.dirF (I := I) (M := M) g (Psi r) v))
        (hPsisr r) D hD).symm)]
    ring
  have hZ : (Work.Diff.EXT.dirF (I := I) (M := M) g
        (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) v x
      - (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1) (Fin.cons v Psi) x
          + ∑ r : Fin (l + 3), Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
              (Function.update Psi r (Work.Diff.EXT.dirF (I := I) (M := M) g (Psi r) v)) x)) = 0 := by
    have horth : ∀ i : Fin (Module.finrank ℝ E),
        g.inner x (Work.Diff.EXT.dirF (I := I) (M := M) g
            (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) v x
          - (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1) (Fin.cons v Psi) x
              + ∑ r : Fin (l + 3), Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
                  (Function.update Psi r (Work.Diff.EXT.dirF (I := I) (M := M) g (Psi r) v)) x))
          (W i x) = 0 := by
      intro i
      rw [map_sub, map_add, map_sum, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
      rw [key (W i) (hW i)]
      ring
    have hexp := Work.EXT.sum_inner_smul_eq_self_of_isONFrame g x (fun i => W i x) hONx
      (Work.Diff.EXT.dirF (I := I) (M := M) g
          (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) v x
        - (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1) (Fin.cons v Psi) x
            + ∑ r : Fin (l + 3), Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
                (Function.update Psi r (Work.Diff.EXT.dirF (I := I) (M := M) g (Psi r) v)) x))
    rw [Finset.sum_congr rfl (fun i _ => by rw [horth i, zero_smul])] at hexp
    simpa using hexp.symm
  exact sub_eq_zero.mp hZ

/-! ## The main theorem -/

theorem atomExtStepW
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (hON : Work.Diff.EXT.evolX.OnFrameAtPlaceholder (I := I) (M := M) g x W)
    (m l N : ℕ) (s : Fin (m + 4))
    (κ : Fin (m + 4) → Fin N) (ξ : Fin (l + 3) → Fin N)
    (hgood : Work.Diff.EXT.evolX.GoodDataN m l N s κ ξ)
    (F : Fin (N + 1) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ u, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (F u)) :
    Work.Diff.EXT.extStep (I := I) (M := M) g
        (Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W m l N s κ ξ) F x
      = Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W (m + 1) l (N + 1) (Fin.succ s)
          (Fin.cons 0 (fun i : Fin (m + 4) => Fin.succ (κ i)))
          (fun r : Fin (l + 3) => Fin.succ (ξ r)) F x
        + Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W m (l + 1) (N + 1) s
          (fun i : Fin (m + 4) => Fin.succ (κ i))
          (Fin.cons 0 (fun r : Fin (l + 3) => Fin.succ (ξ r))) F x := by
  classical
  rw [Work.Diff.EXT.extStep]
  set S : (Fin N → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
    Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W m l N s κ ξ with hS
  set G : Fin N → Work.Diff.EXT.TField (I := I) (M := M) := fun u : Fin N => F u.succ with hG
  set Psi : Fin (l + 3) → Work.Diff.EXT.TField (I := I) (M := M) :=
    fun r : Fin (l + 3) => G (ξ r) with hPsi
  set A : Work.Diff.EXT.TField (I := I) (M := M) :=
    Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi with hA
  set Z2 : Work.Diff.EXT.TField (I := I) (M := M) :=
    Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1) (Fin.cons (F 0) Psi) with hZ2
  set Tt : Fin (m + 4) → Work.Diff.EXT.TField (I := I) (M := M) :=
    fun i : Fin (m + 4) => if i = s then A else G (κ i) with hTt
  have hGs : ∀ u : Fin N, Work.Diff.EXT.SmoothF (G u) := fun u => hF u.succ
  have hPsis : ∀ r : Fin (l + 3), Work.Diff.EXT.SmoothF (Psi r) := fun r => hGs (ξ r)
  have hAs : Work.Diff.EXT.SmoothF A :=
    Work.Diff.EXT.evolX.smTf_Zf (I := I) (M := M) hLC g W hW l Psi hPsis
  have hTts : ∀ i : Fin (m + 4), Work.Diff.EXT.SmoothF (Tt i) := by
    intro i
    by_cases hi : i = s
    · have h : Tt i = A := by
        show (if i = s then A else G (κ i)) = A
        rw [if_pos hi]
      rw [h]; exact hAs
    · have h : Tt i = G (κ i) := by
        show (if i = s then A else G (κ i)) = G (κ i)
        rw [if_neg hi]
      rw [h]; exact hGs (κ i)
  have hmv : mvfderiv I (S G) x (F 0 x)
      = Work.Diff.EXT.ckt g (m + 1) (Fin.cons (F 0) Tt) x
        + ∑ i : Fin (m + 4), Work.Diff.EXT.ckt g m
            (Function.update Tt i (Work.Diff.EXT.dirF g (Tt i) (F 0))) x := by
    have h := Work.Diff.EXT.mvfderiv_ckt_T2 (I := I) (M := M) g m Tt (F 0) x
    exact h
  have hkappa : ∀ (i : Fin (m + 4)) (hi : i ≠ s),
      S (Function.update G (κ i) (Work.Diff.EXT.dirF g (G (κ i)) (F 0))) x
        = Work.Diff.EXT.ckt g m (Function.update Tt i (Work.Diff.EXT.dirF g (Tt i) (F 0))) x := by
    intro i hi
    have hTi : Tt i = G (κ i) := by
      show (if i = s then A else G (κ i)) = G (κ i)
      rw [if_neg hi]
    rw [hTi]
    refine congrArg (fun tu : Fin (m + 4) → Work.Diff.EXT.TField (I := I) (M := M) =>
      Work.Diff.EXT.ckt g m tu x) ?_
    show (fun j : Fin (m + 4) => if j = s then Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
          (fun r : Fin (l + 3) =>
            Function.update G (κ i) (Work.Diff.EXT.dirF g (G (κ i)) (F 0)) (ξ r))
        else Function.update G (κ i) (Work.Diff.EXT.dirF g (G (κ i)) (F 0)) (κ j))
      = Function.update Tt i (Work.Diff.EXT.dirF g (G (κ i)) (F 0))
    exact atomStep_kappa m l N s κ ξ hgood.1 hgood.2.2.1 g W G i hi _
  have hxi : ∀ r : Fin (l + 3),
      S (Function.update G (ξ r) (Work.Diff.EXT.dirF g (G (ξ r)) (F 0))) x
        = Work.Diff.EXT.ckt g m (Function.update Tt s (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
            (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0))))) x := by
    intro r
    refine congrArg (fun tu : Fin (m + 4) → Work.Diff.EXT.TField (I := I) (M := M) =>
      Work.Diff.EXT.ckt g m tu x) ?_
    show (fun j : Fin (m + 4) => if j = s then Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
          (fun r' : Fin (l + 3) =>
            Function.update G (ξ r) (Work.Diff.EXT.dirF g (G (ξ r)) (F 0)) (ξ r'))
        else Function.update G (ξ r) (Work.Diff.EXT.dirF g (G (ξ r)) (F 0)) (κ j))
      = Function.update Tt s (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
          (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0))))
    exact atomStep_xi m l N s κ ξ hgood.2.2.1 hgood.2.1 g W G r _
  have hcorr : (∑ u : Fin N, S (Function.update G u (Work.Diff.EXT.dirF g (G u) (F 0))) x)
      = (∑ i ∈ (Finset.univ.erase s : Finset (Fin (m + 4))),
            Work.Diff.EXT.ckt g m
              (Function.update Tt i (Work.Diff.EXT.dirF g (Tt i) (F 0))) x)
        + ∑ r : Fin (l + 3), Work.Diff.EXT.ckt g m (Function.update Tt s
            (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
              (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0))))) x := by
    rw [Work.Diff.EXT.evolX.sum_split_of_goodDataN hgood
      (fun u => S (Function.update G u (Work.Diff.EXT.dirF g (G u) (F 0))) x)]
    rw [Finset.sum_congr rfl (fun i hi => hkappa i (Finset.mem_erase.mp hi).1),
        Finset.sum_congr rfl (fun r _ => hxi r)]
  have herase : (∑ i : Fin (m + 4), Work.Diff.EXT.ckt g m
        (Function.update Tt i (Work.Diff.EXT.dirF g (Tt i) (F 0))) x)
      = (∑ i ∈ (Finset.univ.erase s : Finset (Fin (m + 4))),
            Work.Diff.EXT.ckt g m
              (Function.update Tt i (Work.Diff.EXT.dirF g (Tt i) (F 0))) x)
        + Work.Diff.EXT.ckt g m (Function.update Tt s (Work.Diff.EXT.dirF g (Tt s) (F 0))) x := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (m + 4)))
      (fun i => Work.Diff.EXT.ckt g m
        (Function.update Tt i (Work.Diff.EXT.dirF g (Tt i) (F 0))) x) (Finset.mem_univ s)]
  have hconsPsis : ∀ r : Fin (l + 1 + 3),
      Work.Diff.EXT.SmoothF
        ((Fin.cons (F 0) Psi : Fin (l + 1 + 3) → Work.Diff.EXT.TField (I := I) (M := M)) r) := by
    intro r
    induction r using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hF 0
    | succ r' => rw [Fin.cons_succ]; exact hPsis r'
  have hZ2s : Work.Diff.EXT.SmoothF Z2 :=
    Work.Diff.EXT.evolX.smTf_Zf (I := I) (M := M) hLC g W hW (l + 1) (Fin.cons (F 0) Psi) hconsPsis
  have hYs : ∀ r : Fin (l + 3), Work.Diff.EXT.SmoothF
      (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
        (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0)))) := by
    intro r
    refine Work.Diff.EXT.evolX.smTf_Zf (I := I) (M := M) hLC g W hW l _ ?_
    intro r'
    by_cases hr : r' = r
    · rw [hr]
      show Work.Diff.EXT.SmoothF
        (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0)) r)
      rw [Function.update_apply, if_pos rfl]
      exact Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g (hPsis r) (hF 0)
    · rw [Function.update_of_ne hr]; exact hPsis r'
  have hYeq : (∑ r : Fin (l + 3), (1 : ℝ) • Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
        (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0))))
      = ∑ r : Fin (l + 3), Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
        (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0))) :=
    Finset.sum_congr rfl (fun r _ => one_smul ℝ _)
  have hYsm : Work.Diff.EXT.SmoothF (∑ r : Fin (l + 3),
      Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
        (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0)))) := by
    rw [← hYeq]
    exact smoothF_sum_smul Finset.univ (fun _ : Fin (l + 3) => (1 : ℝ))
      (fun r => Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
        (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0)))) hYs
  have hleib : Work.Diff.EXT.ckt g m (Function.update Tt s (Work.Diff.EXT.dirF g (Tt s) (F 0))) x
      = Work.Diff.EXT.ckt g m (Function.update Tt s Z2) x
        + ∑ r : Fin (l + 3), Work.Diff.EXT.ckt g m (Function.update Tt s
            (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
              (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0))))) x := by
    have hTs : Tt s = A := by
      show (if s = s then A else G (κ s)) = A
      rw [if_pos rfl]
    have hzf := zfLeibnizSelf (I := I) (M := M) hLC g x W hW hON l Psi hPsis (F 0) (hF 0)
    have hval : Work.Diff.EXT.dirF g (Tt s) (F 0) x
        = (Z2 + ∑ r : Fin (l + 3), Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
            (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0)))) x := by
      rw [hTs]
      show Work.Diff.EXT.dirF g
          (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Psi) (F 0) x
        = (Z2 + ∑ r : Fin (l + 3), Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
            (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0)))) x
      rw [Pi.add_apply, Finset.sum_apply]
      exact hzf
    have hupd := Work.Diff.EXT.ckt_val_dep hLC g m x hTts s
      (Work.Diff.EXT.dirF_smooth hLC g (hTts s) (hF 0))
      (Work.Diff.EXT.smoothF_add hZ2s hYsm) hval
    rw [hupd]
    rw [show Work.Diff.EXT.ckt g m (Function.update Tt s
          (Z2 + ∑ r : Fin (l + 3), Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
            (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0))))) x
        = Work.Diff.EXT.ckt g m (Function.update Tt s Z2) x
          + Work.Diff.EXT.ckt g m (Function.update Tt s
            (∑ r : Fin (l + 3), Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
              (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0))))) x from
      congrFun (Work.Diff.EXT.TensProp_add hLC g (Work.Diff.EXT.tensProp_all hLC g m)
        hTts s hZ2s hYsm) x]
    congr 1
    rw [← hYeq]
    rw [Work.Diff.EXT.evolX.ckt_sum_slot hLC g Tt hTts s (fun _ : Fin (l + 3) => (1 : ℝ))
      (fun r => Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
        (Function.update Psi r (Work.Diff.EXT.dirF g (Psi r) (F 0)))) hYs x]
    simp only [one_mul]
  have hmain : mvfderiv I (S G) x (F 0 x)
        - ∑ u : Fin N, S (Function.update G u (Work.Diff.EXT.dirF g (G u) (F 0))) x
      = Work.Diff.EXT.ckt g (m + 1) (Fin.cons (F 0) Tt) x
        + Work.Diff.EXT.ckt g m (Function.update Tt s Z2) x := by
    rw [hmv, hcorr, herase, hleib]
    ring
  have htu1 : (fun i : Fin (m + 1 + 4) => if i = Fin.succ s then
          Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l (fun r : Fin (l + 3) => F (Fin.succ (ξ r)))
        else F (@Fin.cons (m + 4) (fun _ => Fin (N + 1)) (0 : Fin (N + 1))
          (fun i : Fin (m + 4) => Fin.succ (κ i)) i))
      = (Fin.cons (F 0) Tt : Fin (m + 1 + 4) → Work.Diff.EXT.TField (I := I) (M := M)) := by
    funext i
    induction i using Fin.cases with
    | zero =>
      rw [Fin.cons_zero, if_neg (Fin.succ_ne_zero s).symm]
      simp only [Fin.cons_zero]
    | succ j =>
      simp only [Fin.cons_succ]
      by_cases hj : j = s
      · rw [if_pos (congrArg Fin.succ hj)]
        show Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l
            (fun r : Fin (l + 3) => F (Fin.succ (ξ r))) = (if j = s then A else G (κ j))
        rw [if_pos hj]
      · rw [if_neg (fun hh => hj (Fin.succ_inj.mp hh))]
        show F (Fin.succ (κ j)) = (if j = s then A else G (κ j))
        rw [if_neg hj]
  have hA1 : Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W (m + 1) l (N + 1) (Fin.succ s)
        (Fin.cons 0 (fun i : Fin (m + 4) => Fin.succ (κ i)))
        (fun r : Fin (l + 3) => Fin.succ (ξ r)) F x
      = Work.Diff.EXT.ckt g (m + 1) (Fin.cons (F 0) Tt) x := by
    rw [Work.Diff.EXT.evolX.Atom]
    exact congrArg (fun tu : Fin (m + 1 + 4) → Work.Diff.EXT.TField (I := I) (M := M) =>
      Work.Diff.EXT.ckt g (m + 1) tu x) htu1
  have htu2 : (fun i : Fin (m + 4) => if i = s then
          Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1)
            (fun r : Fin (l + 1 + 3) =>
              F (@Fin.cons (l + 3) (fun _ => Fin (N + 1)) (0 : Fin (N + 1))
                (fun r : Fin (l + 3) => Fin.succ (ξ r)) r))
        else F (Fin.succ (κ i)))
      = (Function.update Tt s Z2 : Fin (m + 4) → Work.Diff.EXT.TField (I := I) (M := M)) := by
    funext i
    by_cases hi : i = s
    · rw [hi]
      show (if s = s then Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1)
            (fun r : Fin (l + 1 + 3) =>
              F (@Fin.cons (l + 3) (fun _ => Fin (N + 1)) (0 : Fin (N + 1))
                (fun r : Fin (l + 3) => Fin.succ (ξ r)) r))
          else F (Fin.succ (κ s))) = Function.update Tt s Z2 s
      rw [if_pos rfl, Function.update_apply, if_pos rfl]
      have harg : (Fin.cons (F 0) Psi : Fin (l + 1 + 3) → Work.Diff.EXT.TField (I := I) (M := M))
          = (fun r : Fin (l + 1 + 3) =>
              F (@Fin.cons (l + 3) (fun _ => Fin (N + 1)) (0 : Fin (N + 1))
                (fun r : Fin (l + 3) => Fin.succ (ξ r)) r)) := by
        funext r
        induction r using Fin.cases with
        | zero => simp only [Fin.cons_zero]
        | succ r' => simp only [Fin.cons_succ]; rfl
      show Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1)
          (fun r : Fin (l + 1 + 3) =>
            F (@Fin.cons (l + 3) (fun _ => Fin (N + 1)) (0 : Fin (N + 1))
              (fun r : Fin (l + 3) => Fin.succ (ξ r)) r))
        = Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1) (Fin.cons (F 0) Psi)
      rw [harg]
    · rw [Function.update_of_ne hi]
      show (if i = s then Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W (l + 1)
            (fun r : Fin (l + 1 + 3) =>
              F (@Fin.cons (l + 3) (fun _ => Fin (N + 1)) (0 : Fin (N + 1))
                (fun r : Fin (l + 3) => Fin.succ (ξ r)) r)) else F (Fin.succ (κ i)))
          = (if i = s then A else G (κ i))
      rw [if_neg hi, if_neg hi]
  have hA2 : Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W m (l + 1) (N + 1) s
        (fun i : Fin (m + 4) => Fin.succ (κ i))
        (Fin.cons 0 (fun r : Fin (l + 3) => Fin.succ (ξ r))) F x
      = Work.Diff.EXT.ckt g m (Function.update Tt s Z2) x := by
    rw [Work.Diff.EXT.evolX.Atom]
    exact congrArg (fun tu : Fin (m + 4) → Work.Diff.EXT.TField (I := I) (M := M) =>
      Work.Diff.EXT.ckt g m tu x) htu2
  rw [hmain, hA1, hA2]

end Work.Diff.EXT.evolX

import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarTraceDefs
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Work.Diff.EXT.jetSmoothDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trace form of the connection-variation pairing

The target `Work.Diff.EXT.evolX.connVar_pair_trace` computes the `a`-th jet of the frame-traced
level-`1` curvature tower

`cvTr0ρ g ef ρ Z y = ∑ m ckt g 1 (cvHins (a := 0) ρ Z (ef m)) y`.

The content is that covariant differentiation commutes with the trace over the frame: the `a`-th jet
of the trace is the level-`(a+1)` tower evaluated on the tuples in which the frame fields fill the two
traced curvature slots.

The proof is the induction `Work.Diff.EXT.evolX.jetAll_TOp_all` on the jet order, whose step
`Work.Diff.EXT.evolX.TOp_step` moves the frame slots one position and produces, at each step, two
"extra" Leibniz corrections coming from the frame slots; these cancel in the sum over the frame
(`Work.Diff.EXT.evolX.frameSlot_cancel_field`) because the frame velocity is skew-adjoint while the
two curvature slots traced against the frame sum are symmetric.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

open Trace

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## `ckt` at a point is `Kpt` on the values of the tuple -/

theorem ckt_eq_Kpt_v (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    {T : Fin (k + 4) → TField (I := I) (M := M)} (hT : ∀ s, SmoothF (T s)) :
    ckt g k T x = Kpt g x k (fun s => T s x) := by
  rw [Kpt]
  exact ckt_val_dep_all (I := I) (M := M) hLC g k x hT
    (fun s => Work.Diff.GE.smoothExt_cmdiff x (T s x))
    (fun s => by rw [Work.Diff.GE.smoothExt_apply])

/-! ## Skewness of the frame velocity -/

/-- The frame velocity coefficients are skew (metric compatibility of the Levi-Civita connection
against an orthonormal frame). -/
theorem frameVel_skew_v (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    {ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)} (hef : ∀ m, SmoothF (ef m))
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun m => ef m y))
    {X : TField (I := I) (M := M)} (hX : SmoothF X) (m p : Fin (Module.finrank ℝ E)) :
    g.inner x (lcOf g (ef m) x (X x)) (ef p x) + g.inner x (lcOf g (ef p) x (X x)) (ef m x) = 0 := by
  have h := Work.Diff.GE.covRic_frame_skew (I := I) (M := M) hLC g x (X x) ef hef hON m p
  rw [← g.symm x (lcOf g (ef p) x (X x)) (ef m x)] at h
  exact h

/-! ## The cancellation of the two frame-slot corrections (value level) -/

theorem frameSlot_cancel_val (hLC : LCSmooth I M) (g : SMet I M) (x : M) (n : ℕ)
    (ρ : Fin 3 ≃ Fin 3)
    {G : Fin (n + 3) → TField (I := I) (M := M)} (hG : ∀ i, SmoothF (G i))
    {ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)} (hef : ∀ m, SmoothF (ef m))
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun m => ef m y))
    {X : TField (I := I) (M := M)} (hX : SmoothF X)
    (hskew : ∀ m p : Fin (Module.finrank ℝ E),
      g.inner x (lcOf g (ef m) x (X x)) (ef p x)
        + g.inner x (lcOf g (ef p) x (X x)) (ef m x) = 0) :
    (∑ m : Fin (Module.finrank ℝ E), Kpt g x (n + 1)
        (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot0 n)
          (lcOf g (ef m) x (X x))))
      + (∑ m : Fin (Module.finrank ℝ E), Kpt g x (n + 1)
        (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot1 n)
          (lcOf g (ef m) x (X x)))) = 0 := by
  classical
  by_cases hfr : 0 < Module.finrank ℝ E
  · have hONx : IsONFrame g x (fun i => ef i x) := hON.self_of_nhds
    have hexp : ∀ m : Fin (Module.finrank ℝ E), lcOf g (ef m) x (X x)
        = ∑ p, g.inner x (lcOf g (ef m) x (X x)) (ef p x) • ef p x :=
      fun m => (Work.Diff.GE.sum_smul_inner_eq_self g x hfr (fun i => ef i x) hONx
        (lcOf g (ef m) x (X x))).symm
    have hcb : ∀ m p : Fin (Module.finrank ℝ E),
        g.inner x (lcOf g (ef m) x (X x)) (ef p x)
          = - g.inner x (lcOf g (ef p) x (X x)) (ef m x) := by
      intro m p
      have h := hskew m p
      linarith
    have hP : (∑ m : Fin (Module.finrank ℝ E), Kpt g x (n + 1)
          (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot0 n)
            (lcOf g (ef m) x (X x))))
        = ∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            g.inner x (lcOf g (ef m) x (X x)) (ef p x)
              * Kpt g x (n + 1) (fun r => cvHins2 ρ G (ef p) (ef m) r x) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      conv_lhs => rw [hexp m]
      rw [show Kpt g x (n + 1) (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot0 n)
            (∑ p, g.inner x (lcOf g (ef m) x (X x)) (ef p x) • ef p x))
          = KptLin hLC g x (n + 1)
              (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot0 n)
                (∑ p, g.inner x (lcOf g (ef m) x (X x)) (ef p x) • ef p x)) from rfl]
      rw [MultilinearMap.map_update_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [MultilinearMap.map_update_smul, smul_eq_mul]
      refine congrArg (fun W : Fin (n + 5) → TangentSpace I x =>
        g.inner x (lcOf g (ef m) x (X x)) (ef p x) * Kpt g x (n + 1) W) ?_
      rw [show Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot0 n) (ef p x)
          = (fun r => cvHins2 ρ G (ef p) (ef m) r x) from by
        rw [← update_pointwise (I := I) (M := M) (cvHins ρ G (ef m)) (cvUslot0 n) (ef p) x,
          update_cvHins_uslot0']]
    have hQ : (∑ m : Fin (Module.finrank ℝ E), Kpt g x (n + 1)
          (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot1 n)
            (lcOf g (ef m) x (X x))))
        = ∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            g.inner x (lcOf g (ef m) x (X x)) (ef p x)
              * Kpt g x (n + 1) (fun r => cvHins2 ρ G (ef m) (ef p) r x) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      conv_lhs => rw [hexp m]
      rw [show Kpt g x (n + 1) (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot1 n)
            (∑ p, g.inner x (lcOf g (ef m) x (X x)) (ef p x) • ef p x))
          = KptLin hLC g x (n + 1)
              (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot1 n)
                (∑ p, g.inner x (lcOf g (ef m) x (X x)) (ef p x) • ef p x)) from rfl]
      rw [MultilinearMap.map_update_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [MultilinearMap.map_update_smul, smul_eq_mul]
      refine congrArg (fun W : Fin (n + 5) → TangentSpace I x =>
        g.inner x (lcOf g (ef m) x (X x)) (ef p x) * Kpt g x (n + 1) W) ?_
      rw [show Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot1 n) (ef p x)
          = (fun r => cvHins2 ρ G (ef m) (ef p) r x) from by
        rw [← update_pointwise (I := I) (M := M) (cvHins ρ G (ef m)) (cvUslot1 n) (ef p) x,
          update_cvHins_uslot1']]
    rw [hP, hQ]
    exact Work.Diff.GE.covRic_skew_sum_zero
      (fun m p => g.inner x (lcOf g (ef m) x (X x)) (ef p x))
      (fun m p => Kpt g x (n + 1) (fun r => cvHins2 ρ G (ef m) (ef p) r x))
      hcb
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hfr
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]

/-! ## The cancellation of the two frame-slot corrections (field level) -/

theorem frameSlot_cancel_field (hLC : LCSmooth I M) (g : SMet I M) (x : M) (n : ℕ)
    (ρ : Fin 3 ≃ Fin 3)
    {G : Fin (n + 3) → TField (I := I) (M := M)} (hG : ∀ i, SmoothF (G i))
    {ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)} (hef : ∀ m, SmoothF (ef m))
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun m => ef m y))
    {X : TField (I := I) (M := M)} (hX : SmoothF X)
    (hskew : ∀ m p : Fin (Module.finrank ℝ E),
      g.inner x (lcOf g (ef m) x (X x)) (ef p x)
        + g.inner x (lcOf g (ef p) x (X x)) (ef m x) = 0) :
    (∑ m : Fin (Module.finrank ℝ E), ckt g (n + 1)
        (Function.update (cvHins ρ G (ef m)) (cvUslot0 n) (dirF g (ef m) X)) x)
      + (∑ m : Fin (Module.finrank ℝ E), ckt g (n + 1)
        (Function.update (cvHins ρ G (ef m)) (cvUslot1 n) (dirF g (ef m) X)) x) = 0 := by
  have h1 : ∀ m : Fin (Module.finrank ℝ E), ckt g (n + 1)
        (Function.update (cvHins ρ G (ef m)) (cvUslot0 n) (dirF g (ef m) X)) x
      = Kpt g x (n + 1) (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot0 n)
          (lcOf g (ef m) x (X x))) := by
    intro m
    rw [ckt_eq_Kpt_v (I := I) (M := M) hLC g (n + 1) x
      (T := Function.update (cvHins ρ G (ef m)) (cvUslot0 n) (dirF g (ef m) X))
      (hT := fun r => by
        by_cases h : r = cvUslot0 n
        · rw [h, Function.update_self]
          exact dirF_smooth (I := I) (M := M) hLC g (hef m) hX
        · rw [Function.update_of_ne h]
          exact cvHins_smooth (I := I) (M := M) G hG (hef m) r)]
    exact congrArg (fun W : Fin (n + 5) → TangentSpace I x => Kpt g x (n + 1) W)
      (update_pointwise (I := I) (M := M) (cvHins ρ G (ef m)) (cvUslot0 n)
        (dirF g (ef m) X) x)
  have h2 : ∀ m : Fin (Module.finrank ℝ E), ckt g (n + 1)
        (Function.update (cvHins ρ G (ef m)) (cvUslot1 n) (dirF g (ef m) X)) x
      = Kpt g x (n + 1) (Function.update (fun r => cvHins ρ G (ef m) r x) (cvUslot1 n)
          (lcOf g (ef m) x (X x))) := by
    intro m
    rw [ckt_eq_Kpt_v (I := I) (M := M) hLC g (n + 1) x
      (T := Function.update (cvHins ρ G (ef m)) (cvUslot1 n) (dirF g (ef m) X))
      (hT := fun r => by
        by_cases h : r = cvUslot1 n
        · rw [h, Function.update_self]
          exact dirF_smooth (I := I) (M := M) hLC g (hef m) hX
        · rw [Function.update_of_ne h]
          exact cvHins_smooth (I := I) (M := M) G hG (hef m) r)]
    exact congrArg (fun W : Fin (n + 5) → TangentSpace I x => Kpt g x (n + 1) W)
      (update_pointwise (I := I) (M := M) (cvHins ρ G (ef m)) (cvUslot1 n)
        (dirF g (ef m) X) x)
  rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_congr rfl (fun m _ => h2 m)]
  exact frameSlot_cancel_val (I := I) (M := M) hLC g x n ρ hG hef hON hX hskew

/-! ## The slot identity of one step of the tower -/

theorem TOp_step_bracket {n : ℕ} (g : SMet I M) (ρ : Fin 3 ≃ Fin 3)
    {ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)}
    (i : Fin (Module.finrank ℝ E))
    {G : Fin (n + 3) → TField (I := I) (M := M)}
    {X : TField (I := I) (M := M)} (y : M) :
    (∑ u : Fin (n + 5), ckt g (n + 1)
        (Function.update (cvHins ρ G (ef i)) u (dirF g (cvHins ρ G (ef i) u) X)) y)
      = (∑ s : Fin (n + 3), ckt g (n + 1)
          (cvHins ρ (Function.update G s (dirF g (G s) X)) (ef i)) y)
        + ckt g (n + 1)
            (Function.update (cvHins ρ G (ef i)) (cvUslot0 n) (dirF g (ef i) X)) y
        + ckt g (n + 1)
            (Function.update (cvHins ρ G (ef i)) (cvUslot1 n) (dirF g (ef i) X)) y := by
  set H : Fin (n + 5) → ℝ := fun u => ckt g (n + 1)
      (Function.update (cvHins ρ G (ef i)) u (dirF g (cvHins ρ G (ef i) u) X)) y with hH
  have hHu : ∀ u : Fin (n + 5), H u = ckt g (n + 1)
      (Function.update (cvHins ρ G (ef i)) u (dirF g (cvHins ρ G (ef i) u) X)) y :=
    fun u => by simp only [hH]
  change (∑ u : Fin (n + 5), H u) = _
  rw [cv_sum_univ_Hins' ρ H]
  have h1 : (∑ s : Fin (n + 3), H (cvHpos n ρ s)) = ∑ s : Fin (n + 3),
      ckt g (n + 1) (cvHins ρ (Function.update G s (dirF g (G s) X)) (ef i)) y := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hHu (cvHpos n ρ s),
      show dirF g (cvHins ρ G (ef i) (cvHpos n ρ s)) X = dirF g (G s) X from by
        rw [cvHins_hpos'],
      cvHins_update']
  have h2 : H (cvUslot0 n) = ckt g (n + 1)
      (Function.update (cvHins ρ G (ef i)) (cvUslot0 n) (dirF g (ef i) X)) y := by
    rw [hHu (cvUslot0 n), cvHins_uslot0']
  have h3 : H (cvUslot1 n) = ckt g (n + 1)
      (Function.update (cvHins ρ G (ef i)) (cvUslot1 n) (dirF g (ef i) X)) y := by
    rw [hHu (cvUslot1 n), cvHins_uslot1']
  rw [h1, h2, h3]

/-! ## The step of the frame-traced tower -/

theorem TOp_step {n : ℕ} (hLC : LCSmooth I M) (g : SMet I M) (ρ : Fin 3 ≃ Fin 3)
    {ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)} (hef : ∀ m, SmoothF (ef m))
    {x : M} (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun m => ef m y))
    {F : Fin (3 + (n + 1)) → TField (I := I) (M := M)} (hF : ∀ i, SmoothF (F i)) :
    extStep (I := I) (M := M) g
        (fun (G : Fin (3 + n) → TField (I := I) (M := M)) (y : M) =>
          ∑ i, TOpJ g n ρ (ef i) G y) F
      =ᶠ[𝓝 x] (fun y : M => ∑ i, TOpJ g (n + 1) ρ (ef i) F y) := by
  classical
  obtain ⟨V, hVopen, hxV, hV⟩ : ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ z ∈ V, IsONFrame g z (fun i => ef i z) := by
    obtain ⟨U, hU, hUsub⟩ := Filter.eventually_iff_exists_mem.mp hON
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
    exact ⟨V, hVopen, hxV, fun z hz => hUsub z (hVU hz)⟩
  have hVmem : V ∈ 𝓝 x := mem_nhds_iff.mpr ⟨V, subset_rfl, hVopen, hxV⟩
  filter_upwards [hVmem] with y hyV
  have hVy : ∀ᶠ z in 𝓝 y, IsONFrame g z (fun i => ef i z) :=
    Filter.mem_of_superset (hVopen.mem_nhds hyV) (fun z hz => hV z hz)
  set Ft : Fin (3 + n) → TField (I := I) (M := M) := fun i => F (Fin.succ i) with hFt
  set Hn : Fin (n + 3) → TField (I := I) (M := M) :=
    fun i' => F (cvCast3 (n + 1) (Fin.succ i')) with hHn
  have hFtHn : (fun i' : Fin (n + 3) => Ft (cvCast3 n i')) = Hn := by
    funext i'
    exact congrArg F (Fin.ext rfl)
  have hHns : ∀ i, SmoothF (Hn i) := fun i' => hF _
  have hX0 : SmoothF (F 0) := hF 0
  rw [Work.Diff.EXT.extStep]
  rw [← hFt]
  change (mvfderiv I (fun y' : M => ∑ i, TOpJ g n ρ (ef i) Ft y') y (F 0 y)
      - ∑ s : Fin (3 + n), ∑ i, TOpJ g n ρ (ef i)
          (Function.update Ft s (dirF g (Ft s) (F 0))) y)
    = ∑ i, TOpJ g (n + 1) ρ (ef i) F y
  have hterm : ∀ i : Fin (Module.finrank ℝ E), TOpJ g (n + 1) ρ (ef i) F y
      = mvfderiv I (fun y' : M => ckt g (n + 1) (cvHins ρ Hn (ef i)) y') y (F 0 y)
        - ∑ u : Fin (n + 5), ckt g (n + 1)
            (Function.update (cvHins ρ Hn (ef i)) u
              (dirF g (cvHins ρ Hn (ef i) u) (F 0))) y := by
    intro i
    have hcs := Work.Diff.EXT.ckt_succ (I := I) (M := M) g (n + 1)
      (cvHins (a := n + 1) ρ (fun i' : Fin ((n + 1) + 3) => F (cvCast3 (n + 1) i')) (ef i))
    have htailPt : ∀ c : Fin (n + 5),
        cvHins (a := n + 1) ρ (fun i' : Fin ((n + 1) + 3) => F (cvCast3 (n + 1) i'))
          (ef i) c.succ = cvHins ρ Hn (ef i) c := by
      intro c
      have h := congrFun (cvDrop0_cvHins' (a := n) ρ
        (fun i' : Fin ((n + 1) + 3) => F (cvCast3 (n + 1) i')) (ef i)) c
      simp only [cvDrop0] at h
      have h2 : (fun i'' : Fin (n + 3) =>
          (fun i' : Fin ((n + 1) + 3) => F (cvCast3 (n + 1) i')) (Fin.succ i'')) = Hn := rfl
      rw [h, h2]
    have hhead : cvHins (a := n + 1) ρ
        (fun i' : Fin ((n + 1) + 3) => F (cvCast3 (n + 1) i')) (ef i) 0 = F 0 := by
      rw [cvHins_zero' (a := n + 1) (by omega) ρ _ (ef i)]
      rfl
    rw [TOpJ_apply', hcs]
    simp only [Pi.sub_apply, Finset.sum_apply, htailPt, hhead]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_sub_distrib]
  have hmv : mvfderiv I (fun y' : M => ∑ i : Fin (Module.finrank ℝ E),
        TOpJ g n ρ (ef i) Ft y') y (F 0 y)
      = ∑ i : Fin (Module.finrank ℝ E),
          mvfderiv I (fun y' : M => ckt g (n + 1) (cvHins ρ Hn (ef i)) y') y (F 0 y) := by
    have hfun : (fun y' : M => ∑ i : Fin (Module.finrank ℝ E), TOpJ g n ρ (ef i) Ft y')
        = (fun y' : M => ∑ i : Fin (Module.finrank ℝ E),
            ckt g (n + 1) (cvHins ρ Hn (ef i)) y') := by
      funext y'
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TOpJ_apply', hFtHn]
    rw [hfun]
    rw [show (fun y' : M => ∑ i : Fin (Module.finrank ℝ E),
          ckt g (n + 1) (cvHins ρ Hn (ef i)) y')
        = (fun y' : M => ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
            ckt g (n + 1) (cvHins ρ Hn (ef i)) y') from by simp]
    rw [Work.Diff.GE.Kato3.mvfderiv_sum (t := Finset.univ)
      (F := fun (i : Fin (Module.finrank ℝ E)) (y' : M) =>
        ckt g (n + 1) (cvHins ρ Hn (ef i)) y')
      (hF := fun i => (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g (n + 1) _
        (cvHins_smooth (I := I) (M := M) Hn hHns (hef i))).1) y (F 0 y)]
  rw [hmv]
  have hb : ∀ i : Fin (Module.finrank ℝ E),
      (∑ u : Fin (n + 5), ckt g (n + 1)
          (Function.update (cvHins ρ Hn (ef i)) u
            (dirF g (cvHins ρ Hn (ef i) u) (F 0))) y)
        = (∑ σ : Fin (n + 3), ckt g (n + 1)
            (cvHins ρ (Function.update Hn σ (dirF g (Hn σ) (F 0))) (ef i)) y)
          + ckt g (n + 1)
              (Function.update (cvHins ρ Hn (ef i)) (cvUslot0 n) (dirF g (ef i) (F 0))) y
          + ckt g (n + 1)
              (Function.update (cvHins ρ Hn (ef i)) (cvUslot1 n) (dirF g (ef i) (F 0))) y :=
    fun i => TOp_step_bracket (n := n) g ρ i (G := Hn) (X := F 0) y
  have hcancel : (∑ i : Fin (Module.finrank ℝ E),
        (ckt g (n + 1)
            (Function.update (cvHins ρ Hn (ef i)) (cvUslot0 n) (dirF g (ef i) (F 0))) y
          + ckt g (n + 1)
            (Function.update (cvHins ρ Hn (ef i)) (cvUslot1 n) (dirF g (ef i) (F 0))) y)) = 0 := by
    rw [Finset.sum_add_distrib]
    exact frameSlot_cancel_field (I := I) (M := M) hLC g y n ρ hHns hef hVy hX0
      (fun m p => frameVel_skew_v (I := I) (M := M) hLC g y hef hVy hX0 m p)
  have hkey : (∑ i : Fin (Module.finrank ℝ E), ∑ u : Fin (n + 5), ckt g (n + 1)
        (Function.update (cvHins ρ Hn (ef i)) u
          (dirF g (cvHins ρ Hn (ef i) u) (F 0))) y)
      = (∑ σ : Fin (n + 3), ∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
          (cvHins ρ (Function.update Hn σ (dirF g (Hn σ) (F 0))) (ef i)) y) := by
    calc (∑ i : Fin (Module.finrank ℝ E), ∑ u : Fin (n + 5), ckt g (n + 1)
          (Function.update (cvHins ρ Hn (ef i)) u
            (dirF g (cvHins ρ Hn (ef i) u) (F 0))) y)
        = ∑ i : Fin (Module.finrank ℝ E),
            ((∑ σ : Fin (n + 3), ckt g (n + 1)
                (cvHins ρ (Function.update Hn σ (dirF g (Hn σ) (F 0))) (ef i)) y)
              + ckt g (n + 1)
                  (Function.update (cvHins ρ Hn (ef i)) (cvUslot0 n)
                    (dirF g (ef i) (F 0))) y
              + ckt g (n + 1)
                  (Function.update (cvHins ρ Hn (ef i)) (cvUslot1 n)
                    (dirF g (ef i) (F 0))) y) := Finset.sum_congr rfl (fun i _ => hb i)
      _ = ((∑ i : Fin (Module.finrank ℝ E), ∑ σ : Fin (n + 3), ckt g (n + 1)
              (cvHins ρ (Function.update Hn σ (dirF g (Hn σ) (F 0))) (ef i)) y)
            + (∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
                (Function.update (cvHins ρ Hn (ef i)) (cvUslot0 n) (dirF g (ef i) (F 0))) y))
            + (∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
                (Function.update (cvHins ρ Hn (ef i)) (cvUslot1 n)
                  (dirF g (ef i) (F 0))) y) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ((∑ σ : Fin (n + 3), ∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
              (cvHins ρ (Function.update Hn σ (dirF g (Hn σ) (F 0))) (ef i)) y)
            + (∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
                (Function.update (cvHins ρ Hn (ef i)) (cvUslot0 n) (dirF g (ef i) (F 0))) y))
            + (∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
                (Function.update (cvHins ρ Hn (ef i)) (cvUslot1 n)
                  (dirF g (ef i) (F 0))) y) := by
          rw [Finset.sum_comm]
      _ = (∑ σ : Fin (n + 3), ∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
              (cvHins ρ (Function.update Hn σ (dirF g (Hn σ) (F 0))) (ef i)) y)
            + ((∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
                (Function.update (cvHins ρ Hn (ef i)) (cvUslot0 n) (dirF g (ef i) (F 0))) y)
              + (∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
                (Function.update (cvHins ρ Hn (ef i)) (cvUslot1 n)
                  (dirF g (ef i) (F 0))) y)) := by ring
      _ = (∑ σ : Fin (n + 3), ∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
              (cvHins ρ (Function.update Hn σ (dirF g (Hn σ) (F 0))) (ef i)) y) + 0 := by
          rw [← Finset.sum_add_distrib, hcancel]
      _ = _ := add_zero _
  have hcorr : (∑ s : Fin (3 + n), ∑ i : Fin (Module.finrank ℝ E),
        TOpJ g n ρ (ef i) (Function.update Ft s (dirF g (Ft s) (F 0))) y)
      = (∑ σ : Fin (n + 3), ∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
          (cvHins ρ (Function.update Hn σ (dirF g (Hn σ) (F 0))) (ef i)) y) := by
    have hstep : ∀ s : Fin (3 + n), (∑ i : Fin (Module.finrank ℝ E),
          TOpJ g n ρ (ef i) (Function.update Ft s (dirF g (Ft s) (F 0))) y)
        = (∑ i : Fin (Module.finrank ℝ E), ckt g (n + 1)
            (cvHins ρ (Function.update Hn (cvCast3' n s)
              (dirF g (Hn (cvCast3' n s)) (F 0))) (ef i)) y) := by
      intro s
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TOpJ_apply',
        show (fun i' : Fin (n + 3) =>
              (Function.update Ft s (dirF g (Ft s) (F 0))) (cvCast3 n i'))
            = Function.update Hn (cvCast3' n s) (dirF g (Hn (cvCast3' n s)) (F 0)) from by
          have hFeq : Ft s = Hn (cvCast3' n s) := rfl
          rw [update_comp_cvCast3, hFtHn, hFeq]]
    rw [Finset.sum_congr rfl (fun s _ => hstep s)]
    exact Fintype.sum_bijective (cvCast3' n) (cvCast3'_bijective n) _ _ (fun s => rfl)
  rw [hcorr]
  rw [← hkey]

/-! ## The induction: the `j`-th jet of the trace is the level-`j` frame-traced tower -/

theorem jetAll_TOp_all (hLC : LCSmooth I M) (g : SMet I M) (ρ : Fin 3 ≃ Fin 3)
    {ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)} (hef : ∀ m, SmoothF (ef m))
    {x : M} (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun m => ef m y)) :
    ∀ (j : ℕ) (F : Fin (3 + j) → TField (I := I) (M := M)),
      (∀ i, SmoothF (F i)) →
      jetAll g j 3 (cvTr0ρ g ef ρ) F =ᶠ[𝓝 x] (fun y => ∑ i, TOpJ g j ρ (ef i) F y) := by
  intro j
  induction j with
  | zero =>
      intro F hF
      filter_upwards with y
      simp only [Work.Diff.EXT.jetAll, cvTr0ρ, TOpJ_apply']
      refine Finset.sum_congr rfl fun m _ => ?_
      refine congrArg (fun W : Fin (0 + 3) → TField (I := I) (M := M) =>
        ckt g 1 (cvHins (a := 0) ρ W (ef m)) y) ?_
      funext i
      exact congrArg F (Fin.ext rfl)
  | succ l ih =>
      intro F hF
      have hstep : jetAll g (l + 1) 3 (cvTr0ρ g ef ρ) F
          = extStep (I := I) (M := M) g (jetAll g l 3 (cvTr0ρ g ef ρ)) F := rfl
      rw [hstep]
      have hcongr := Work.Diff.EXT.extStep_congr_at (I := I) (M := M) g
        (jetAll g l 3 (cvTr0ρ g ef ρ))
        (fun (G : Fin (3 + l) → TField (I := I) (M := M)) (y : M) =>
          ∑ i, TOpJ g l ρ (ef i) G y) F x
        (ih (fun i : Fin (3 + l) => F i.succ) (fun i => hF i.succ))
        (fun s : Fin (3 + l) => ih (Function.update (fun i : Fin (3 + l) => F i.succ) s
            (dirF g ((fun i : Fin (3 + l) => F i.succ) s) (F 0)))
          (smoothF_update' (fun i => hF i.succ) s
            (dirF_smooth (I := I) (M := M) hLC g (hF s.succ) (hF 0))))
      refine hcongr.trans ?_
      exact TOp_step (I := I) (M := M) (n := l) hLC g ρ hef hON (F := F) hF

end Work.Diff.EXT.evolX

namespace Work.Diff.EXT.evolX

open Trace

theorem connVar_pair_trace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M)
    {ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hef : Work.Diff.EXT.IsFrameNear (I := I) (M := M) g x ef)
    (ρ : Fin 3 ≃ Fin 3) (a : ℕ)
    (F : Fin (a + 3) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    (Work.Diff.EXT.jetAll g a 3 (Work.Diff.EXT.evolX.cvTr0ρ (I := I) (M := M) g ef ρ)
        (fun r : Fin (3 + a) => F (Work.Diff.EXT.evolX.cvCast3' a r))) =ᶠ[nhds x]
      (fun y => ∑ m : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (a + 1)
        (Work.Diff.EXT.evolX.cvHins (a := a) ρ F (ef m)) y) := by
  classical
  have h := jetAll_TOp_all (I := I) (M := M) hLC g ρ hef.1 hef.2 a
    (fun r : Fin (3 + a) => F (cvCast3' a r)) (fun r => hF _)
  filter_upwards [h] with y hy
  rw [hy]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [TOpJ_apply',
    show (fun i' : Fin (a + 3) => (fun r : Fin (3 + a) => F (cvCast3' a r)) (cvCast3 a i'))
      = F from funext fun i' => congrArg F (cvCast3'_cvCast3 i')]

end Work.Diff.EXT.evolX

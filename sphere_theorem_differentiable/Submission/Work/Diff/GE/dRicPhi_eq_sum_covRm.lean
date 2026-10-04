import Mathlib
import Submission.Work.Diff.Evol.RicDeriv
import Submission.Work.Diff.Evol.RicPhi
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.linearIndependent_of_isONFrame
import Submission.Work.Diff.GE.RL.covRm_linear_fst
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.kato_geodesic_frame
import Submission.Work.Diff.GE.sum_bilinear_antisymm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Work.Diff.Evol

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- If every frame vector `W m x` is annihilated by the linear map `(lcOf g) (W j) x`, then that
linear map vanishes: the `W m x` form an orthonormal (hence basis-sized, hence spanning) family. -/
theorem lcOf_geodesic_frame_zero (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hON : IsONFrame g x (fun m => W m x))
    (hgeo : ∀ m j, lcOf g (W j) x (W m x) = 0) (j : Fin (Module.finrank ℝ E)) :
    lcOf g (W j) x = 0 := by
  set L : TangentSpace I x →L[ℝ] TangentSpace I x := lcOf g (W j) x with hL
  have hli : LinearIndependent ℝ (fun m => W m x) :=
    linearIndependent_of_isONFrame g x (fun m => W m x) hON
  have htop : Submodule.span ℝ (Set.range (fun m => W m x)) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hli, Fintype.card_fin]
    rfl
  have hle : Submodule.span ℝ (Set.range (fun m => W m x)) ≤ LinearMap.ker L.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact hgeo m j
  ext v
  exact hle (htop ▸ Submodule.mem_top)

/-- **A smooth orthonormal frame near a point, starting from the chosen frame at the point.**
There are globally smooth vector fields `W i` (`i : Fin (finrank ℝ E)`) which are `g`-orthonormal
near `x` and which satisfy `W i x = onFrame g x i`.

This is the Gram--Schmidt frame of `Work.Diff.GE.kato_geodesic_frame`, but starting from the
smooth extensions `smoothExt x (onFrame g x i)` (no jet correction) and without asking for the
frame to be geodesic at `x`.  We avoid `Work.Diff.GE.kato_geodesic_frame` here because its proof
currently rests on the (still unproved) lemma `Work.Diff.GE.kato_jet_correction`. -/
theorem exists_smooth_onframe (g : SMet I M) (x : M) :
    ∃ W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y),
      (∀ i, CMDiff ∞ (T% (W i))) ∧
      (∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y)) ∧
      (∀ i, W i x = onFrame g x i) := by
  classical
  set e : katoIdx E → TangentSpace I x := onFrame g x with hedef
  have he : IsONFrame g x e := isONFrame_onFrame g x
  let V : katoIdx E → Π y : M, TangentSpace I y := fun i => smoothExt x (e i)
  have hVs : ∀ i, CMDiff ∞ (T% (V i)) := fun i => smoothExt_cmdiff x (e i)
  have hVx : ∀ i, V i x = e i := fun i => smoothExt_apply x (e i)
  have key : ∀ m : ℕ, ∀ i : katoIdx E, i.val < m →
      (CMDiff ∞ (T% (katoFrame g x V i)))
      ∧ (katoFrame g x V i x = V i x)
      ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1)
      ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
          g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hIH : ∀ j, j.val < i.val →
            (CMDiff ∞ (T% (katoFrame g x V j)))
            ∧ (katoFrame g x V j x = V j x)
            ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1)
            ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < j.val →
                g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0) :=
          fun j hj => ih j (by rw [← heq]; exact hj)
        obtain ⟨hUs, hGs⟩ :=
          kato_smooth g V (katoFrame g x V) i (hVs i) (fun j hj => (hIH j hj).1)
        have hON : ∀ j, j.val < i.val → g.inner x (V i x) (V j x) = 0 := by
          intro j hj
          have hne : i ≠ j := by
            intro hij; rw [← hij] at hj; exact absurd hj (Nat.lt_irrefl _)
          rw [hVx i, hVx j, he i j, ite_eq_right hne]
        have hUx : katoU g V (katoFrame g x V) i x = V i x :=
          katoU_apply_x g x V (katoFrame g x V) i (fun j hj => (hIH j hj).2.1) hON
        have hV1 : g.inner x (V i x) (V i x) = 1 := by
          rw [hVx i, he i i, ite_eq_left rfl]
        have hfx : 0 < katoGram g V (katoFrame g x V) i x := by
          rw [katoGram_apply_x g x V (katoFrame g x V) i hUx hV1]; norm_num
        obtain ⟨hFpos, hFs, hCs, hCeq, hFx, hFeq⟩ :=
          kato_smooth_norm g x V (katoFrame g x V) i hGs hfx
        have hCx : katoC g x V (katoFrame g x V) i x = 1 :=
          katoC_apply_x g x V (katoFrame g x V) i
            (by rw [hFx, katoGram_apply_x g x V (katoFrame g x V) i hUx hV1])
        have hWx : katoFrame g x V i x = V i x := by
          rw [katoFrame_eq g x V i]
          show katoC g x V (katoFrame g x V) i x • katoU g V (katoFrame g x V) i x = V i x
          rw [hCx, hUx, one_smul]
        have hWs : CMDiff ∞ (T% (katoFrame g x V i)) := by
          rw [katoFrame_eq g x V i]
          exact hCs.smul_section hUs
        have hdiag_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.1] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hoff_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val → ∀ k, k.val < j.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hbump1 : ∀ᶠ y in 𝓝 x,
            katoBump (I := I) (katoGram g V (katoFrame g x V) i) x y = 1 :=
          (katoBump_spec hGs hfx).2.2.2.2
        have hfpos_ev : ∀ᶠ y in 𝓝 x, 0 < katoGram g V (katoFrame g x V) i y :=
          (hGs x).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hfx)
        have hdiag_i : ∀ᶠ y in 𝓝 x,
            g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).1
        have hoff_i : ∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
            g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          intro k hk
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).2 k hk
        exact ⟨hWs, hWx, hdiag_i, hoff_i⟩
  refine ⟨katoFrame g x V, ?_, ?_, ?_⟩
  · intro i
    exact (key (i.val + 1) i (Nat.lt_succ_self _)).1
  · refine isONFrame_of_diag_off g x (katoFrame g x V) ?_ ?_
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.1
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2
  · intro i
    rw [(key (i.val + 1) i (Nat.lt_succ_self _)).2.1]
    exact hVx i



/-- **Expansion of a vector in an orthonormal frame**, without any non-degeneracy hypothesis on
the dimension: for an orthonormal family `e` of `TₓM` indexed by `Fin (finrank ℝ E)`,
`∑ i, ⟪v, e i⟫ • e i = v`.  When `finrank ℝ E = 0` both sides are `0`. -/
theorem sum_smul_inner_eq_self_gen (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (v : TangentSpace I x) :
    ∑ i, g.inner x v (e i) • e i = v := by
  by_cases hn : 0 < Module.finrank ℝ E
  · exact sum_smul_inner_eq_self g x hn e he v
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hv : v = 0 := finrank_zero_iff_forall_zero.mp h0 v
    subst hv
    simp [h0]

/-- The `Ext` pattern `dRicPhi` of `∇Ric` (`Work.Diff.Evol.RicPhi`) is the metric trace of `∇Rm`,
for ARBITRARY smooth fields `Y`, `Z` in its two slots:
  `dRicPhi g x v Y Z = ∑_m covRm g x v (e_m) (Y x) (e_m) (Z x)`  with `e = onFrame g x`.
The pointwise trace identity `ricAt (lcOf g) y u v = ∑_m rmP g y (e m) u (e m) v` for an
orthonormal frame is the hypothesis `htr`.  Route: take the smooth frame `W` of
`Work.Diff.GE.exists_smooth_onframe` (smooth, `IsONFrame` near `x`, `W i x = onFrame g x i`);
the functions `ricF g Y Z` and `y ↦ ∑ m, rmP g y (W m y) (Y y) (W m y) (Z y)` agree near `x` by
`htr`; computing the derivative of the second one with the definition of `Work.Diff.GE.dRmPhi`
leaves the `Rm(∇_v W_m, ...)` corrections, which cancel because the frame is orthonormal in a
neighbourhood (`Work.Diff.GE.sum_bilinear_antisymm`, with the antisymmetry `ω m j + ω j m = 0` of
the connection coefficients coming from metric compatibility), and the `∇_v Y`, `∇_v Z` corrections
are exactly the two `ricAt` corrections in the definition of `Work.Diff.Evol.dRicPhi` by `htr`.
The remaining term is `∑ m, dRmPhi g x v (W m) Y (W m) Z`, which is
`∑ m, covRm g x v (W m x) (Y x) (W m x) (Z x)` by `Work.Diff.GE.Kato3.covRm_field_form`. -/
theorem dRicPhi_eq_sum_covRm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (htr : ∀ (g : Submission.Diff.SMet I M) (y : M)
        (e : Fin (Module.finrank ℝ E) → TangentSpace I y),
        Submission.Diff.IsONFrame g y e →
          ∀ u v : TangentSpace I y,
            Submission.Diff.ricAt (Submission.Diff.lcOf g) y u v
              = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
                  (fun m => Submission.Diff.rmP g y (e m) u (e m) v))
    (g : Submission.Diff.SMet I M) (x : M) (v : TangentSpace I x)
    (Y Z : Π y : M, TangentSpace I y)
    (hY : Work.Diff.GE.SmoothField (I := I) (M := M) Y)
    (hZ : Work.Diff.GE.SmoothField (I := I) (M := M) Z) :
    Work.Diff.Evol.dRicPhi g x v Y Z
      = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) (Y x)
            (Submission.Diff.onFrame g x m) (Z x)) := by
  classical
  obtain ⟨W, hWs, hONev, hWx⟩ := exists_smooth_onframe (I := I) (M := M) g x
  have hONx : IsONFrame g x (fun m => W m x) := by
    have h : (fun i : Fin (Module.finrank ℝ E) => W i x) = onFrame g x := funext hWx
    rw [h]; exact isONFrame_onFrame g x
  -- expansion of a vector in the frame
  have hexp : ∀ a : TangentSpace I x, ∑ j, g.inner x a (W j x) • W j x = a :=
    fun a => sum_smul_inner_eq_self_gen (I := I) (M := M) g x (fun j => W j x) hONx a
  have hA_exp : ∀ m : Fin (Module.finrank ℝ E),
      lcOf g (W m) x v = ∑ j, g.inner x (lcOf g (W m) x v) (W j x) • W j x :=
    fun m => (hexp (lcOf g (W m) x v)).symm
  -- antisymmetry of the connection coefficients, from metric compatibility
  have hantiω : ∀ m j : Fin (Module.finrank ℝ E),
      g.inner x (lcOf g (W m) x v) (W j x)
        + g.inner x (lcOf g (W j) x v) (W m x) = 0 := by
    intro m j
    have hconst : (fun y : M => g.inner y (W m y) (W j y))
        =ᶠ[𝓝 x] (fun _ : M => (if m = j then (1 : ℝ) else 0)) := by
      filter_upwards [hONev] with y hy
      exact hy m j
    have hderiv0 : mvfderiv I (fun y : M => g.inner y (W m y) (W j y)) x v = 0 := by
      rw [mvfderiv_congr_eventuallyEq hconst]
      simp [mvfderiv_const]
    have h := kato_mvfderiv_inner_lc (I := I) (M := M) g x v (hWs m) (hWs j)
    rw [hderiv0] at h
    rw [g.symm x (W m x) (lcOf g (W j) x v)] at h
    exact h.symm
  -- congruence of `ricF g Y Z` with the traced field
  have hcongr : ricF g Y Z =ᶠ[𝓝 x]
      (fun y : M => ∑ m, rmP g y (W m y) (Y y) (W m y) (Z y)) := by
    filter_upwards [hONev] with y hy
    exact htr g y (fun m => W m y) hy (Y y) (Z y)
  have h1 : mvfderiv I (ricF g Y Z) x v
      = mvfderiv I (fun y : M => ∑ m, rmP g y (W m y) (Y y) (W m y) (Z y)) x v :=
    congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_congr_eventuallyEq hcongr)
  have hFs : ∀ m : Fin (Module.finrank ℝ E),
      CMDiff ∞ (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) :=
    fun m => rmP_fields_smooth (I := I) (M := M) hLC g (hWs m) hY (hWs m) hZ
  have h2 : mvfderiv I (fun y : M => ∑ m, rmP g y (W m y) (Y y) (W m y) (Z y)) x v
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v :=
    Kato3.mvfderiv_sum Finset.univ
      (fun m y => rmP g y (W m y) (Y y) (W m y) (Z y)) hFs x v
  -- the per-`m` decomposition
  have hper : ∀ m : Fin (Module.finrank ℝ E),
      mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v
        = dRmPhi g x v (W m) Y (W m) Z
          + rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x)
          + rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x)
          + rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x)
          + rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v) := by
    intro m
    simp only [dRmPhi]
    ring
  have hsum : (∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v)
      = (∑ m, dRmPhi g x v (W m) Y (W m) Z)
        + (∑ m, rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v)) := by
    rw [show (∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v)
        = ∑ m, (dRmPhi g x v (W m) Y (W m) Z
          + rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x)
          + rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x)
          + rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x)
          + rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v)) from
      Finset.sum_congr rfl (fun m _ => hper m)]
    simp only [Finset.sum_add_distrib]
  -- the two `∇_v Y`, `∇_v Z` corrections are the two `ricAt` terms of `dRicPhi`
  have hc2 : (∑ m, rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x))
      = ricAt (lcOf g) x (lcOf g Y x v) (Z x) := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [hWx m])]
    exact (htr g x (onFrame g x) (isONFrame_onFrame g x) (lcOf g Y x v) (Z x)).symm
  have hc4 : (∑ m, rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v))
      = ricAt (lcOf g) x (Y x) (lcOf g Z x v) := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [hWx m])]
    exact (htr g x (onFrame g x) (isONFrame_onFrame g x) (Y x) (lcOf g Z x v)).symm
  -- the two `∇_v W_m` corrections cancel
  have hanti_sum :
      (∑ m, rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x)) = 0 := by
    have hB₁ : ∀ (r s : ℝ) (u₁ u₂ w : TangentSpace I x),
        rmP g x (r • u₁ + s • u₂) (Y x) w (Z x)
          = r * rmP g x u₁ (Y x) w (Z x) + s * rmP g x u₂ (Y x) w (Z x) := by
      intro r s u₁ u₂ w
      rw [rmP_add_fst g hLC x, rmP_smul_fst g hLC x, rmP_smul_fst g hLC x]
    have hB₂ : ∀ (r s : ℝ) (u w₁ w₂ : TangentSpace I x),
        rmP g x u (Y x) (r • w₁ + s • w₂) (Z x)
          = r * rmP g x u (Y x) w₁ (Z x) + s * rmP g x u (Y x) w₂ (Z x) := by
      intro r s u w₁ w₂
      rw [rmP_add_thd g hLC x, rmP_smul_thd g hLC x, rmP_smul_thd g hLC x]
    have hmain := sum_bilinear_antisymm (V := TangentSpace I x)
      (B := fun u w => rmP g x u (Y x) w (Z x)) hB₁ hB₂
      (fun m => W m x) (fun m => lcOf g (W m) x v)
      (fun m j => g.inner x (lcOf g (W m) x v) (W j x)) hA_exp hantiω
    rw [Finset.sum_add_distrib] at hmain
    exact hmain
  have hcomb : (∑ m, dRmPhi g x v (W m) Y (W m) Z)
        + (∑ m, rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v))
      = (∑ m, dRmPhi g x v (W m) Y (W m) Z)
        + ricAt (lcOf g) x (lcOf g Y x v) (Z x)
        + ricAt (lcOf g) x (Y x) (lcOf g Z x v) := by
    rw [hc2, hc4]
    linarith [hanti_sum]
  have hGd : mvfderiv I (ricF g Y Z) x v
      = (∑ m, dRmPhi g x v (W m) Y (W m) Z)
        + ricAt (lcOf g) x (lcOf g Y x v) (Z x)
        + ricAt (lcOf g) x (Y x) (lcOf g Z x v) := by
    rw [h1, h2, hsum, hcomb]
  have h3 : dRicPhi g x v Y Z = (∑ m, dRmPhi g x v (W m) Y (W m) Z) := by
    simp only [dRicPhi]
    rw [hGd]
    ring
  rw [h3]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [(Kato3.covRm_field_form (I := I) (M := M) hLC g x v (hWs m) hY (hWs m) hZ).symm, hWx m]

end Work.Diff.GE

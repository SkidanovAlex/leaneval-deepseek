/-
  WilE9 / Sharp / ExFst — `exFst_sol_eq`: the `s`-coordinate of a solution of the pulled-back
  system is the value of `f`.

  This is the last step of the *forward* direction of `exSemiPf_fst`.  Its input is

  * a point `w` of an effectively smooth stratum `E` whose projection is the `ψ`-image of
    `(x, f x)`;
  * a family `Y` of points of the pulled-back ambient, continuous at `x`, agreeing with the
    reconstructed point `exFib (exPt w x (f x) σ)` at `x`, and satisfying the *structural*
    relations of the ψ-transport (`y i = ψ x i`, `τ = ψ s`) near `x`;
  * the equations of the pulled-back system near `x`.

  The conclusion is `s = f`.

  The argument is a two-step localization.  Reading the pulled-back point through the
  stratum's own coordinates gives a point `q x' = pbStrat (Fin.append x' (Y x'))` which is
  continuous in `x'` with `q x = w`, and the pulled-back equations which mention the stratum
  (`pbF` at the block `2n+2 … 2n+m+2`) say exactly that the stratum's equations `E.h` vanish at
  `q x'`.  Hence, near `x`, `q x' ∈ E.X.set` by effective smoothness (`E.Good`), and so
  `stratProj (q x') ∈ Zset` by `hπ`.  But the structural relations identify
  `stratProj (q x')` with `ψ (Fin.snoc x' (Y x' fS))`, and `Zset` is the ψ-image of the graph of
  `f`; reading the last coordinate gives `Y x' fS = f x'`.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.ExFst.Defs
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.eaEval_pbRaise
import Submission.Work.WilE9.Psi.psi_psig_algebra

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Work.WilE9.Sharp.ExFst

open WilkiesDesign WilkiesDesign.E

/-! ## 1. Coordinate bookkeeping

The pulled-back ambient `ℝ^{Npb n m}` splits as the base `ℝⁿ` followed by the fibre
`(s, y, w, τ, u, aux)`.  Reading a stratum coordinate (`y`, `τ`, `aux`) of a point of the
pulled-back ambient and then embedding it back into the right half of the ambient is what the
following helpers compute. -/

/-- `ψ a / psig a = a`: the `x`-coordinate recovered from the `(ψ, psig)`-pair. -/
theorem psi_div_psig (a : ℝ) : WilkiesDesign.E.psi a / Work.WilE9.psig a = a := by
  rw [(Work.WilE9.Psi.psi_psig_algebra a).1]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Work.WilE9.Psi.psig_pos a))

/-- The ambient point `(x, y)` of the pulled-back ambient, typed as `Fin (Npb n m) → ℝ`.

`Fin.append x y` has type `Fin (n + qpb n m) → ℝ`, which is *definitionally* the right one but
not *syntactically* equal to `Fin (Npb n m) → ℝ`; `Npb` is a semireducible definition, and the
rewrite tactics match only up to reducible unfolding.  Wrapping `Fin.append` in a definition
declared *at* `Fin (Npb n m) → ℝ` makes every term in sight syntactically homogeneous. -/
def pbAmbPt {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) : Fin (Npb n m) → ℝ :=
  Fin.append x y

@[simp] theorem pbAmbPt_pbY {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    pbAmbPt x y (pbY n m i) = y (fY n m i) := by
  rw [pbAmbPt, ← natAdd_fY (n := n) (m := m) i, Fin.append_right]

@[simp] theorem pbAmbPt_pbT {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    pbAmbPt x y (pbT n m) = y (fT n m) := by
  rw [pbAmbPt, ← natAdd_fT (n := n) (m := m), Fin.append_right]

/-- Coordinatewise, `ψ` of `Fin.snoc x t` is `Fin.snoc (ψ x) (ψ t)`. -/
theorem psiV_snoc {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    WilkiesDesign.E.psiV (Fin.snoc x t) =
      Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi t) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp only [WilkiesDesign.E.psiV]
    rw [Fin.snoc_last, Fin.snoc_last]
  · intro i
    simp only [WilkiesDesign.E.psiV]
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl

/-- The row-embedding of the stratum's ambient into the `*`-piece ambient is the identity on
values. -/
theorem stratInj_castAdd {n m : ℕ} (i : Fin (n + 1)) :
    stratInj (Fin.castAdd m i) = ⟨i.val, by have := i.isLt; omega⟩ := by
  apply Fin.ext
  simp only [stratInj, Fin.val_cast, Fin.val_castAdd]

/-- `stratProj` reads off a coordinate by value. -/
theorem stratProj_eq {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (j : Fin (n + 1)) :
    stratProj w j = w ⟨j.val, by have := j.isLt; omega⟩ := by
  show w (stratInj (Fin.castAdd m j)) = w _
  rw [stratInj_castAdd]

/-- The `y`-coordinates of the pulled-back stratum of `z`. -/
theorem stratProj_pbStrat_castSucc {n m : ℕ} (z : Fin (Npb n m) → ℝ) (i : Fin n) :
    stratProj (pbStrat z) (Fin.castSucc i) = z (pbY n m i) := by
  show z (sIdxPb n m (stratInj (Fin.castAdd m (Fin.castSucc i)))) = z (pbY n m i)
  congr 1
  rw [show stratInj (Fin.castAdd m (Fin.castSucc i))
        = ⟨i.val, by have := i.isLt; omega⟩ from by
    apply Fin.ext; simp only [stratInj, Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc]]
  simp only [sIdxPb]
  rw [dite_eq_left i.isLt]

/-- The `τ`-coordinate of the pulled-back stratum of `z`. -/
theorem stratProj_pbStrat_last {n m : ℕ} (z : Fin (Npb n m) → ℝ) :
    stratProj (pbStrat z) (Fin.last n) = z (pbT n m) := by
  show z (sIdxPb n m (stratInj (Fin.castAdd m (Fin.last n)))) = z (pbT n m)
  congr 1
  rw [show stratInj (Fin.castAdd m (Fin.last n)) = ⟨n, by omega⟩ from by
    apply Fin.ext; simp only [stratInj, Fin.val_cast, Fin.val_castAdd, Fin.val_last]]
  simp only [sIdxPb]
  rw [dite_eq_right (by omega : ¬ ((n : ℕ) < n))]
  rfl

/-! ## 2. The stratum coordinates of a pulled-back point -/

/-- The stratum's coordinates `y`, `τ`, `aux` always land in the *right* half
`Fin (qpb n m)` of the pulled-back ambient. -/
theorem le_sIdxPb_val {n m : ℕ} (i : Fin (n + (1 + m))) : n ≤ (sIdxPb n m i).val := by
  simp only [sIdxPb]
  split_ifs with h1 h2
  · simp only [pbY]; omega
  · simp only [pbT]; omega
  · simp only [pbA]; omega

/-- The fibre index of the `i`-th stratum coordinate of a pulled-back point. -/
def stratFibIdx {n m : ℕ} (i : Fin (n + (1 + m))) : Fin (qpb n m) :=
  ⟨(sIdxPb n m i).val - n, by
    have h1 := le_sIdxPb_val i
    have h2 : (sIdxPb n m i).val < n + qpb n m := by
      have := (sIdxPb n m i).isLt; simpa [Npb] using this
    omega⟩

theorem sIdxPb_eq_natAdd_stratFibIdx {n m : ℕ} (i : Fin (n + (1 + m))) :
    sIdxPb n m i = Fin.natAdd n (stratFibIdx i) := by
  apply Fin.ext
  simp only [stratFibIdx, Fin.val_natAdd]
  have := le_sIdxPb_val i; omega

/-- Reading a pulled-back point at a stratum coordinate is reading the corresponding fibre
coordinate. -/
theorem pbStrat_append_apply {n m : ℕ} (x' : Fin n → ℝ) (Y : Fin (qpb n m) → ℝ)
    (i : Fin (n + (1 + m))) :
    pbStrat (Fin.append x' Y) i = Y (stratFibIdx i) := by
  show Fin.append x' Y (sIdxPb n m i) = Y (stratFibIdx i)
  rw [sIdxPb_eq_natAdd_stratFibIdx i, Fin.append_right]

/-! ## 3. The stratum block of the pulled-back equations -/

/-- The index of the `a`-th stratum equation inside `pbF`. -/
def pbStratIdx (n m : ℕ) (a : Fin (1 + m)) : Fin (qpb n m) :=
  ⟨2 * n + 2 + a.val, by simp [qpb]; omega⟩

/-- The stratum block of the pulled-back equations is the stratum's own equation, raised. -/
theorem pbF_pbStratIdx {n m r : ℕ} (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (a : Fin (1 + m)) :
    pbF n m r h (pbStratIdx n m a) = pbRaise (n := n) (m := m) (h a) := by
  unfold pbF pbStratIdx
  rw [dite_eq_right (by omega : ¬ (2 * n + 2 + a.val = 0)),
      dite_eq_right (by omega : ¬ (2 * n + 2 + a.val ≤ n)),
      dite_eq_right (by omega : ¬ (2 * n + 2 + a.val ≤ 2 * n)),
      dite_eq_right (by omega : ¬ (2 * n + 2 + a.val = 2 * n + 1))]
  dsimp only
  congr 1
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

/-! ## 4. The theorem -/

theorem exFst_sol_eq {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {Zset : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Zset)
    (E : Work.WilE9.Sharp.EffStratum n m) (hgood : E.Good)
    (Q : Set (Fin (n + (1 + m)) → ℝ))
    (hQ : ∀ z ∈ Q, ∀ᶠ z' in nhds z,
      (∀ a : Fin (1 + m), eaEval E.X.c (E.h a) z' = 0) → z' ∈ Q)
    (hπ : ∀ w ∈ Q, Work.WilE9.Sharp.stratProj w ∈ Zset)
    {x : Fin n → ℝ} {w : Fin (n + (1 + m)) → ℝ} (hw : w ∈ E.X.set) (hwQ : w ∈ Q)
    (hbase : Work.WilE9.Sharp.stratProj w =
      Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi (f x)))
    (σ : ℝ) (Y : (Fin n → ℝ) → (Fin (Work.WilE9.Sharp.qpb n m) → ℝ))
    (hYcd : ContinuousAt Y x)
    (hY0 : Y x = Work.WilE9.Sharp.exFib (Work.WilE9.Sharp.exPt w x (f x) σ))
    (hbr : ∀ᶠ x' in nhds x,
      (∀ i : Fin n, Y x' (Work.WilE9.Sharp.fY n m i) = WilkiesDesign.E.psi (x' i)) ∧
      Y x' (Work.WilE9.Sharp.fT n m) = WilkiesDesign.E.psi (Y x' (Work.WilE9.Sharp.fS n m)))
    (hsol : ∀ᶠ x' in nhds x, ∀ j,
      WilkiesDesign.E.eaEval (Work.WilE9.Sharp.pbChain E.X.c)
        (Work.WilE9.Sharp.pbF n m E.X.r E.h j) (Fin.append x' (Y x')) = 0) :
    ∀ᶠ x' in nhds x, Y x' (Work.WilE9.Sharp.fS n m) = f x' := by
  -- (1) the stratum's equations vanish at `pbStrat (Fin.append x' (Y x'))` near `x`
  have heq : ∀ᶠ x' in nhds x,
      ∀ a : Fin (1 + m), eaEval E.X.c (E.h a) (pbStrat (Fin.append x' (Y x'))) = 0 := by
    filter_upwards [hsol] with x' hx'
    intro a
    have h1 := hx' (pbStratIdx n m a)
    rw [pbF_pbStratIdx E.h a] at h1
    change eaEval (pbChain E.X.c)
      (pbRaise (E.h a)) (pbAmbPt x' (Y x')) = 0 at h1
    rw [eaEval_pbRaise] at h1
    exact h1
  -- (2) `pbStrat (Fin.append · (Y ·))` is continuous at `x`
  have hcont : ContinuousAt (fun x' : Fin n → ℝ => pbStrat (Fin.append x' (Y x'))) x := by
    rw [continuousAt_pi]
    intro i
    have h1 : (fun x' : Fin n → ℝ => pbStrat (Fin.append x' (Y x')) i)
        = fun x' => Y x' (stratFibIdx (n := n) (m := m) i) :=
      funext fun x' => pbStrat_append_apply x' (Y x') i
    rw [h1]
    exact (continuous_apply (stratFibIdx (n := n) (m := m) i)).continuousAt.comp hYcd
  -- (3) its value at `x` is the stratum point `w`
  have hqx : pbStrat (Fin.append x (Y x)) = w := by
    have hexb : exBase (exPt w x (f x) σ) = x := by
      funext i
      rw [exBase_apply, exPt_exY, exPt_exW, wY_of_hbase hbase i, psi_div_psig]
    have hzz : Fin.append x (exFib (exPt w x (f x) σ)) = exSub (exPt w x (f x) σ) := by
      rw [exSub_eq_append, hexb]
    rw [hY0, hzz, pbStrat_exSub, exStrat_exPt]
  have htw : Filter.Tendsto (fun x' : Fin n → ℝ => pbStrat (Fin.append x' (Y x')))
      (nhds x) (nhds w) := by
    have h := hcont.tendsto
    rwa [hqx] at h
  -- (4) hence it lies in `Q` near `x`
  have hXmem : ∀ᶠ x' in nhds x, pbStrat (Fin.append x' (Y x')) ∈ Q := by
    have h1 := htw.eventually (hQ w hwQ)
    filter_upwards [h1, heq] with x' h1' heq'
    exact h1' heq'
  -- (5) its projection is the ψ-image of `(x', Y x' fS)`
  have hproj : ∀ᶠ x' in nhds x,
      stratProj (pbStrat (Fin.append x' (Y x'))) =
        Fin.snoc (WilkiesDesign.E.psiV x')
          (WilkiesDesign.E.psi (Y x' (fS n m))) := by
    filter_upwards [hbr] with x' hx'
    funext j
    refine Fin.lastCases ?_ ?_ j
    · conv_lhs => rw [show (Fin.append x' (Y x') : Fin (Npb n m) → ℝ)
          = pbAmbPt x' (Y x') from rfl]
      rw [stratProj_pbStrat_last (n := n) (m := m), pbAmbPt_pbT,
        Fin.snoc_last]
      exact hx'.2
    · intro i
      conv_lhs => rw [show (Fin.append x' (Y x') : Fin (Npb n m) → ℝ)
          = pbAmbPt x' (Y x') from rfl]
      rw [stratProj_pbStrat_castSucc (n := n) (m := m), pbAmbPt_pbY,
        Fin.snoc_castSucc]
      exact hx'.1 i
  -- (6) `stratProj (…) ∈ Zset`, so `Fin.snoc x' (Y x' fS)` is on the graph of `f`
  have hZmem : ∀ᶠ x' in nhds x, stratProj (pbStrat (Fin.append x' (Y x'))) ∈ Zset := by
    filter_upwards [hXmem] with x' hx'
    exact hπ _ hx'
  filter_upwards [hproj, hZmem] with x' hx'proj hx'Z
  have hmem : Fin.snoc x' (Y x' (fS n m)) ∈ WilkiesDesign.graphOf f := by
    rw [hZ, Set.mem_preimage, psiV_snoc, ← hx'proj]
    exact hx'Z
  simp only [WilkiesDesign.graphOf, Set.mem_setOf_eq] at hmem
  rw [Fin.snoc_last, Fin.init_snoc] at hmem
  exact hmem

end Work.WilE9.Sharp.ExFst

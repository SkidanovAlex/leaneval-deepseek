/-
Copyright: work module for the Elgindi finite-time singularity project.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.SlotSum_dz_le_of

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## `ip4_unfold_bound` at level five with finite-order smoothness

`Work.FTS.TransportS.ip4_unfold_bound` proves, for every level `n`,
`|IPn α n u v| ≤ 3^n · 10^22 · SlotSum α (n+1) u v` under `SmoothOpen u`, `SmoothOpen v`
(`C^∞` on the *open* quadrant).  The bare-`f` `N₀`-row needs the level-five case for a datum
that is only `C⁷` on the open quadrant (its coefficient `L₁₂(f)` is merely
`ContDiffOn ℝ 7`), so this file re-runs the very same induction with the *level-dependent*
finite-order hypothesis `ContDiffOn ℝ (n + 2) (uncurry u) Q0`.

The only analytic input of the unfolding is the shift of a slot along `D_z`, i.e. the
finite-order Clairaut identity
`D_z^bD_θ^a(D_z u) = D_z^{b+1}D_θ^a u` on `Q0` (`SixAux.mixed_dz_eqOn_fin`, obtained from
the `SmoothOpen` version `Work.FTS.TransportS.mixed_dz_eqOn` by tracking the derivative
order), together with the one-order closure of `ContDiffOn` under `D_z`/`D_θ`
(`SixAux.contDiffOn_Dz_le`, `SixAux.contDiffOn_Dth_le`).  The `D_θ`-shift of the slot sum is
hypothesis-free; the `D_z`-shift with the pointwise identity as a hypothesis is
`SlotSum_dz_le_of` (sibling module).  Everything else is the verbatim bookkeeping of
`ip4_unfold_bound`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace SixAux

/-! ## Order bookkeeping for `ContDiffOn` -/

/-- Weakening the order of a `ContDiffOn`-statement. -/
theorem cd_of_le_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} {m n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry G) V) (hmn : m ≤ n) :
    ContDiffOn ℝ m (Function.uncurry G) V :=
  h.of_le (by exact_mod_cast hmn)

/-- `∂_z` costs one order of smoothness on an open set. -/
theorem contDiffOn_pz_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ} {m : ℕ}
    (h : ContDiffOn ℝ (m + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ m (Function.uncurry (Work.Spaces.pz G)) V := by
  have hfd : ContDiffOn ℝ m (fderiv ℝ (Function.uncurry G)) V :=
    h.fderiv_of_isOpen hV (by norm_num)
  have hcomp : ContDiffOn ℝ m
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) ((1 : ℝ), (0 : ℝ))) V :=
    (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ)))).comp_contDiffOn hfd
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pz_eq_fderiv
    ((h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp))

/-- `∂_θ` costs one order of smoothness on an open set. -/
theorem contDiffOn_pth_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ} {m : ℕ}
    (h : ContDiffOn ℝ (m + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ m (Function.uncurry (Work.Spaces.pth G)) V := by
  have hfd : ContDiffOn ℝ m (fderiv ℝ (Function.uncurry G)) V :=
    h.fderiv_of_isOpen hV (by norm_num)
  have hcomp : ContDiffOn ℝ m
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) ((0 : ℝ), (1 : ℝ))) V :=
    (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ)))).comp_contDiffOn hfd
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pth_eq_fderiv
    ((h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp))

/-- `D_z = z∂_z` costs one order of smoothness on an open set. -/
theorem contDiffOn_Dz_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ} {m : ℕ}
    (h : ContDiffOn ℝ (m + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ m (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact contDiffOn_fst.mul (contDiffOn_pz_le hV h)

/-- `D_θ = sin(2θ)∂_θ` costs one order of smoothness on an open set. -/
theorem contDiffOn_Dth_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ} {m : ℕ}
    (h : ContDiffOn ℝ (m + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ m (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  have hsin : ContDiffOn ℝ m (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    ((Real.contDiff_sin.comp
      ((contDiff_const (c := (2 : ℝ))).mul contDiff_snd))).contDiffOn
  exact hsin.mul (contDiffOn_pth_le hV h)

/-- The iterated `D_z^i` costs `i` orders of smoothness on an open set. -/
theorem contDiffOn_DzIter_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i : ℕ) {G : ℝ → ℝ → ℝ} {m : ℕ},
      ContDiffOn ℝ (i + m) (Function.uncurry G) V →
      ContDiffOn ℝ m (Function.uncurry (Work.Spaces.DzIter i G)) V := by
  intro i
  induction i with
  | zero => intro G m h; exact cd_of_le_nat (m := m) (n := 0 + m) h (by omega)
  | succ i ih =>
      intro G m h
      have h1 : ContDiffOn ℝ (i + m + 1 : ℕ) (Function.uncurry G) V :=
        cd_of_le_nat (m := i + m + 1) (n := Nat.succ i + m) h (by omega)
      have h2 : ContDiffOn ℝ (i + m : ℕ) (Function.uncurry (Work.Spaces.Dz G)) V :=
        contDiffOn_Dz_le hV h1
      have h3 : ContDiffOn ℝ m
          (Function.uncurry (Work.Spaces.DzIter i (Work.Spaces.Dz G))) V := ih h2
      rwa [Work.FTS.TransportS.DzIter_comp] at h3

/-- The iterated `D_θ^i` costs `i` orders of smoothness on an open set. -/
theorem contDiffOn_DthIter_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i : ℕ) {G : ℝ → ℝ → ℝ} {m : ℕ},
      ContDiffOn ℝ (i + m) (Function.uncurry G) V →
      ContDiffOn ℝ m (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  intro i
  induction i with
  | zero => intro G m h; exact cd_of_le_nat (m := m) (n := 0 + m) h (by omega)
  | succ i ih =>
      intro G m h
      have h1 : ContDiffOn ℝ (i + m + 1 : ℕ) (Function.uncurry G) V :=
        cd_of_le_nat (m := i + m + 1) (n := Nat.succ i + m) h (by omega)
      have h2 : ContDiffOn ℝ (i + m : ℕ) (Function.uncurry (Work.Spaces.Dth G)) V :=
        contDiffOn_Dth_le hV h1
      have h3 : ContDiffOn ℝ m
          (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dth G))) V := ih h2
      rwa [Work.FTS.TransportS.DthIter_comp] at h3

/-! ## The finite-order Clairaut chain -/

/-- `D_θ` and `D_z` commute at any point where the datum is `C²`. -/
theorem Dth_Dz_apply_fin {X : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ 2 (Function.uncurry X) (z, θ)) :
    Work.Spaces.Dth (Work.Spaces.Dz X) z θ = Work.Spaces.Dz (Work.Spaces.Dth X) z θ :=
  (Work.Spaces.Dz_Dth_comm hX).symm

/-- `D_θ^i(D_z X) = D_z(D_θ^i X)` on the open quadrant, for `X` of class `C^{i+1}`. -/
theorem Dth_Dz_iter_eqOn_fin (i : ℕ) {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ (i + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz X)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i X)))
      Work.FTS.EllipticEst.Q0 := by
  induction i with
  | zero => intro p hp; rfl
  | succ i ih =>
      have h1 : ContDiffOn ℝ (i + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
        cd_of_le_nat (m := i + 1) (n := Nat.succ i + 1) hX (by omega)
      have h2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DthIter i X))
          Work.FTS.EllipticEst.Q0 :=
        contDiffOn_DthIter_le Work.FTS.EllipticEst.isOpen_Q0 i (m := 2)
          (cd_of_le_nat (m := i + 2) (n := Nat.succ i + 1) hX (by omega))
      have hA : Set.EqOn
          (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz X))))
          (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i X))))
          Work.FTS.EllipticEst.Q0 :=
        Work.FTS.TransportS.Dth_congrOn Work.FTS.EllipticEst.isOpen_Q0 (ih h1)
      have hB : Set.EqOn
          (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i X))))
          (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i X))))
          Work.FTS.EllipticEst.Q0 := fun p hp =>
        Dth_Dz_apply_fin (h2.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))
      exact hA.trans hB

/-- **The finite-order slot identity**: on the open quadrant the `z`-derivative slides through
the iterated curvilinear derivatives, needing only `C^{a+b+1}` of `u`. -/
theorem mixed_dz_eqOn_fin {u : ℝ → ℝ → ℝ} (b a : ℕ)
    (hu : ContDiffOn ℝ (a + b + 1) (Function.uncurry u) Work.FTS.EllipticEst.Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0 := by
  have h1 : Set.EqOn (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter a u))) Work.FTS.EllipticEst.Q0 :=
    Dth_Dz_iter_eqOn_fin a (cd_of_le_nat (m := a + 1) (n := a + b + 1) hu (by omega))
  have h2 := Work.FTS.TransportS.DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 h1 b
  intro p hp
  have h4 : Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dz u)) p.1 p.2
      = Work.Spaces.DzIter b (Work.Spaces.Dz (Work.Spaces.DthIter a u)) p.1 p.2 := h2 hp
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dz u)) p.1 p.2
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a u) p.1 p.2
  rw [h4, Work.FTS.TransportS.DzIter_comp]

end SixAux

/-! ## The shifts of the slot sum -/

/-- The `D_θ`-shift of the slot sum needs no smoothness at all (the underlying shift of the
slot pairing is definitional). -/
theorem SlotTerm_dth_le_fin (α : ℝ) (a b : ℕ) (u v : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)
      ≤ Work.FTS.TransportS.SlotTerm α (a + 1) b u v := by
  have heta := Work.FTS.TransportS.slotPairing_dth Work.FTS.TransportS.leafEta a b u v
  have hone := Work.FTS.TransportS.slotPairing_dth Work.FTS.TransportS.leafOne a b u v
  have hgam := Work.FTS.TransportS.slotPairing_dth (Work.FTS.TransportS.leafGam α) a b u v
  have hthird : (if 1 ≤ a then
        |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) (a + 1) b u v|
      else 0)
      ≤ (if 1 ≤ a + 1 then
        |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) (a + 1) b u v|
      else 0) := by
    rw [if_pos (by omega : 1 ≤ a + 1)]
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]
    · rw [if_neg ha]
      exact abs_nonneg _
  unfold Work.FTS.TransportS.SlotTerm
  rw [heta, hone, hgam]
  linarith [hthird]

/-- The `D_θ`-shift of the slot sum at finite order. -/
theorem SlotSum_dth_le_fin (α : ℝ) (n : ℕ) (u v : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.SlotSum α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
      ≤ Work.FTS.TransportS.SlotSum α (n + 1) u v := by
  rw [Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm,
    Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          Work.FTS.TransportS.SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          Work.FTS.TransportS.SlotTerm α (a + 1) b u v :=
        Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun b _ => SlotTerm_dth_le_fin α a b u v))
    _ = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - (a + 1)),
          Work.FTS.TransportS.SlotTerm α (a + 1) b u v := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [show n + 2 - (a + 1) = n + 1 - a from Nat.succ_sub_succ (n := n + 1) (m := a)]
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          Work.FTS.TransportS.SlotTerm α a' b u v := by
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right
          (show (0 : ℝ) ≤ ∑ b ∈ Finset.range (n + 2 - 0),
            Work.FTS.TransportS.SlotTerm α 0 b u v from
            Finset.sum_nonneg (fun b _ => Work.FTS.TransportS.SlotTerm_nonneg α 0 b u v))

/-! ## The unfolding at finite order -/

/-- **The induction of the unfolding at finite order.**  For every `n`, the `n`-fold iterate
of the coercive recursion is dominated by `3^n · 10^22` times the slot sum of level `n + 1`,
under the level-dependent hypothesis that the datum is `C^{n+2}` on the open quadrant. -/
theorem ip4_unfold_bound_fin : ∀ (n : ℕ) (α : ℝ) (u v : ℝ → ℝ → ℝ),
    ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry u) Work.FTS.EllipticEst.Q0 →
    ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry v) Work.FTS.EllipticEst.Q0 →
    |Work.FTS.TransportS.IPn α n u v|
      ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α (n + 1) u v := by
  intro n
  induction n with
  | zero =>
      intro α u v hu hv
      rw [show Work.FTS.TransportS.IPn α 0 = Work.Coercivity.H1IP α from rfl]
      simpa using Work.FTS.TransportS.H1IP_le_SlotSum_one α u v
  | succ n ih =>
      intro α u v hu hv
      have hu' : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry u) Work.FTS.EllipticEst.Q0 :=
        SixAux.cd_of_le_nat (m := n + 2) (n := n + 3) hu (by omega)
      have hv' : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry v) Work.FTS.EllipticEst.Q0 :=
        SixAux.cd_of_le_nat (m := n + 2) (n := n + 3) hv (by omega)
      have hdt : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry (Work.Spaces.Dth u))
          Work.FTS.EllipticEst.Q0 :=
        SixAux.contDiffOn_Dth_le (m := n + 2) Work.FTS.EllipticEst.isOpen_Q0
          (show ContDiffOn ℝ (n + 2 + 1 : ℕ) (Function.uncurry u)
            Work.FTS.EllipticEst.Q0 from hu)
      have hdv : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry (Work.Spaces.Dth v))
          Work.FTS.EllipticEst.Q0 :=
        SixAux.contDiffOn_Dth_le (m := n + 2) Work.FTS.EllipticEst.isOpen_Q0
          (show ContDiffOn ℝ (n + 2 + 1 : ℕ) (Function.uncurry v)
            Work.FTS.EllipticEst.Q0 from hv)
      have hdz : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry (Work.Spaces.Dz u))
          Work.FTS.EllipticEst.Q0 :=
        SixAux.contDiffOn_Dz_le (m := n + 2) Work.FTS.EllipticEst.isOpen_Q0
          (show ContDiffOn ℝ (n + 2 + 1 : ℕ) (Function.uncurry u)
            Work.FTS.EllipticEst.Q0 from hu)
      have hdzu : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry (Work.Spaces.Dz v))
          Work.FTS.EllipticEst.Q0 :=
        SixAux.contDiffOn_Dz_le (m := n + 2) Work.FTS.EllipticEst.isOpen_Q0
          (show ContDiffOn ℝ (n + 2 + 1 : ℕ) (Function.uncurry v)
            Work.FTS.EllipticEst.Q0 from hv)
      have hIHu := ih α u v hu' hv'
      have hIHd := ih α (Work.Spaces.Dth u) (Work.Spaces.Dth v) hdt hdv
      have hIHz := ih α (Work.Spaces.Dz u) (Work.Spaces.Dz v) hdz hdzu
      have hd := SlotSum_dth_le_fin α (n + 1) u v
      have hz : Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
            (Work.Spaces.Dz v)
          ≤ Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v :=
        SlotSum_dz_le_of (n := n + 1)
          (fun a b _ => SixAux.mixed_dz_eqOn_fin b a
            (SixAux.cd_of_le_nat (m := a + b + 1) (n := n + 3) hu (by omega)))
          (fun a b _ => SixAux.mixed_dz_eqOn_fin b a
            (SixAux.cd_of_le_nat (m := a + b + 1) (n := n + 3) hv (by omega)))
      have hmono := Work.FTS.TransportS.SlotSum_mono (α := α) (u := u) (v := v)
        (n := n + 1) (m := n + 1 + 1) (by omega)
      have hsum : Work.FTS.TransportS.SlotSum α (n + 1) u v
            + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
              (Work.Spaces.Dth v)
            + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
              (Work.Spaces.Dz v)
          ≤ 3 * Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v := by
        linarith
      have hstep : Work.FTS.TransportS.IPn α (n + 1) u v
          = Work.FTS.TransportS.IPn α n u v
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v) := by
        rw [show Work.FTS.TransportS.IPn α (n + 1)
              = Work.Coercivity.HkIPStep 1 1 (Work.FTS.TransportS.IPn α n) from rfl]
        simp only [Work.Coercivity.HkIPStep, one_mul]
      rw [hstep]
      have htri : |Work.FTS.TransportS.IPn α n u v
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ |Work.FTS.TransportS.IPn α n u v|
            + |Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := by
        have h1 := abs_add_le
          (Work.FTS.TransportS.IPn α n u v
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v))
          (Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v))
        have h2 := abs_add_le (Work.FTS.TransportS.IPn α n u v)
          (Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v))
        linarith
      have hscale : |Work.FTS.TransportS.IPn α n u v|
            + |Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α (n + 1) u v
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
                (Work.Spaces.Dth v)
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
                (Work.Spaces.Dz v) := by
        linarith
      have hfac : (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α (n + 1) u v
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
                (Work.Spaces.Dth v)
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
                (Work.Spaces.Dz v)
          = (3 : ℝ) ^ n * (10 : ℝ) ^ 22
            * (Work.FTS.TransportS.SlotSum α (n + 1) u v
              + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
                (Work.Spaces.Dth v)
              + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
                (Work.Spaces.Dz v)) := by
        ring
      have hnonneg : (0 : ℝ) ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 := by positivity
      have hfinal : (3 : ℝ) ^ n * (10 : ℝ) ^ 22
            * (Work.FTS.TransportS.SlotSum α (n + 1) u v
              + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
                (Work.Spaces.Dth v)
              + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
                (Work.Spaces.Dz v))
          ≤ (3 : ℝ) ^ (n + 1) * (10 : ℝ) ^ 22
            * Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v := by
        have h3 : (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * (3 * Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v)
            = (3 : ℝ) ^ (n + 1) * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v := by
          rw [pow_succ]; ring
        rw [← h3]
        exact mul_le_mul_of_nonneg_left hsum hnonneg
      linarith [htri, hscale, hfac, hfinal]

/-- `ip4_unfold_bound` at level five with FINITE-ORDER smoothness (`C⁷`) instead of
`SmoothOpen`.  This is what the bare-`f` `N₀`-row needs: there `u = N₀ α (F_* + f) f` has
the coefficient `L₁₂(f)`, which is only `ContDiffOn ℝ 7 (·) (Ioi 0)` (`UopHk.contDiffOn_L12_k`
with `HkMem α 7 f`), and `SmoothOpen (fun z _ => L₁₂ f z)` is NOT available.

ROUTE.  Copy the proof of `TransportS.ip4_unfold_bound`
(`Submission/Work/FTS/TransportS/ip4SlotDomFixed.lean`, line 520), running the induction with
the level-dependent hypothesis `ContDiffOn ℝ (n + 2) (uncurry u) Q0`: the inductive calls at
`(Dth u, Dth v)` and `(Dz u, Dz v)` need `C^{n+2}` of `Dth u` resp. `Dz u`, i.e. `C^{n+3}`
of `u`, and the shift `SlotSum α (n+1) (Dz u) ≤ SlotSum α (n+2) u` is the only place needing
Clairaut (`D_θ D_z = D_z D_θ`: `SixAux.mixed_dz_eqOn_fin`), at derivative order
`a + b + 1 ≤ n + 3`; the `Dth`-shift `mixed b a (Dth u) = mixed b (a+1) u` is definitional.
The base case `H1IP_le_SlotSum_one` has no smoothness hypotheses. -/
theorem ip4UnfoldSix (α : ℝ) (u v : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 7 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ 7 (Function.uncurry v) Work.FTS.EllipticEst.Q0) :
    |Work.FTS.TransportS.IPn α 5 u v|
      ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α 6 u v := by
  exact ip4_unfold_bound_fin 5 α u v hu hv

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux

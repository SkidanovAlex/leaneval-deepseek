import Mathlib
import Submission.Work.OddVolterra.Window.TW2_defs
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.OddVolterra.Window.KvecDefs
import Submission.Work.OddVolterra.Window.KvecJet_data
import Submission.Work.OddVolterra.Window.KvecJet_smooth
import Submission.Work.OddVolterra.Window.JetCurve_box
import Submission.Work.OddVolterra.Window.TWU_aux
import Submission.Work.OddVolterra.Window.TWU_zrad_jet_lipschitz
import Submission.Work.OddVolterra.Window.krad_data
import Submission.Work.OddVolterra.Window.Zrad_jet_bounds
import Submission.Work.OddVolterra.Window.Kvec_deriv_close
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.Window.fed_faaDiBruno_recursion
import Submission.Work.OddVolterra.Window.TW2_qaux
import Submission.Work.OddVolterra.Window.WindowFed
import Submission.Work.OddVolterra.Window.K1M_eq_k1ext
import Submission.Work.OddVolterra.Window.krad_window_data
import Submission.Work.OddVolterra.Window.KJet_mem_box_deriv
import Submission.Work.OddVolterra.Window.KJet_state_lipschitz_window

/-!
# The uniform (in `h`) bound and state-Lipschitz data of the manifest odd Abel kernel `KvecM`

Uniform (in the perturbation `h`) bound `C` and state-Lipschitz constant `M` for the manifest odd
Abel kernel vector `KernelExt.KvecM`, on the square `a, σ ∈ [wLeft, wRight] = [7/10, 19/20]` —
*both* orders of the two slope slots, not only the Volterra range `a ≤ σ` — and for states `z` in
the ball of radius `9/20` around `baseState σ`; this is `KvecMStateData n M C` (`TW2_defs`).

## The route

Both rows of `KvecM n h a σ z = ![- (K₁ z₂ + K₁' z₃), - (K₂ z₂ + K₂' z₃)]` are, at **every**
`a σ` and with no positivity hypothesis, the composition of a *fixed* smooth function of the
finite jet `KJIx n → ℝ` (`KvecDefs`) with the jet curve `u ↦ KJet n h σ z u`:

* the first row uses `K₁M = J₁M / √krad = k1ext` for every `a σ t` (`K1M_eq_k1ext`, from the
  Faà-di-Bruno recursion `Work.Window.fed_faaDiBruno_recursion`), so that it is `KF1 ∘ KJet`
  (`KvecM_row0`);
* the second row is `K₂M = J₂M / √krad` with `J₂M = Rnu ((n:ℝ)-1/2) h lineSlope n`; the jet
  encoding `Rnu_eq_Q` of the Bell recursion (copied into `TW2_qaux`) identifies the numerator with
  `Q ((n:ℝ)-1/2) n` applied to the jet of the pair `(Zrad h (·,σ,t), lineSlope h (·,t))`, and both
  blocks of that jet are read off from `KJet` (`KJblk1_KJet`, `KJblk2_KJet`).  Hence the second row
  is `Phi2 ∘ KJet` (`KvecM_row1`).

`Phi2` is smooth on the open set `KJopen n = {v | 0 < v.kd1 ∧ 0 < v.kd2}` (`contDiffOn_Phi2`), and
on the window every jet value lies in the compact box `KJbox n (KJbz n)`, whose radicand entries
are bounded below by `1/100`:

* the two radicand values at the chord endpoints are in `[1/100, 10]` and their `a`-derivatives
  are bounded by `5` (`krad_window_data`, a version of `krad_data`'s pointwise estimate without
  the order condition `a ≤ σ`);
* the radicand jets are bounded by `KJbz n = 2^{n+2}·100` and the derivatives of `h` by `1/100`
  (`Zrad_jet_bounds` and the jet hypothesis), which gives both the box membership and the bound
  `‖deriv (KJet n h σ z ·) a‖ ≤ KJbz n` (`KJet_mem_box_deriv`).

The remaining two inputs are the compactness lemma `JetCurve_box` (applied to `KF1` and to `Phi2`
on the compact convex box `KJbox n (KJbz n) ⊆ KJopen n`, giving a uniform bound and a uniform
state-Lipschitz constant for both the values and the `a`-derivatives of the two composites) and
the state-Lipschitz property of the jet curve itself, on `u ∈ [9/20, 1]` rather than only on the
Volterra range (`KJet_state_lipschitz_window`).  Assembling the two rows with the sup-norm
estimates on `Fin 2 → ℝ` gives the four inequalities of `KvecMStateData`.

The constant produced by the argument is explicit in principle (`C = max C₁ C₂`,
`M = max C₁ C₂ · Kj`), but the proof only needs its existence.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra

noncomputable section

/-! ## The second row of `KvecM` as a function of the jet

The first row of `KvecM` is already the composition of the fixed smooth function `KF1` of the
finite jet `KJIx n → ℝ` with the jet curve (`KvecDefs`, `KvecJet_smooth`); this holds at *every*
`a` and not only in the Volterra range, because `K1M = k1ext` for all `a σ t`
(`K1M_eq_k1ext`).

The second row, `K2M = J2M / √krad` with `J2M = Rnu ((n:ℝ)-1/2) h lineSlope n`, is *also* a fixed
function of the same finite jet: by the jet encoding of the Bell recursion (`Q`, `Jjet`), the
numerator is `Q ((n:ℝ)-1/2) n` applied to the jet of the pair `(Zrad h (·,σ,t), lineSlope h (·,t))`,
and both blocks of that jet are read off from `KJet` (the `Z1`/`Z2` block and the `w` block of
derivatives of `h` encode exactly the two entries).  This again holds for *every* `a`, with no
positivity hypothesis, since `Rnu_eq_Q` is an identity of real numbers valid everywhere.

This is what lets the whole kernel vector be handled by the compactness lemma `JetCurve_box` on
the compact box `KJbox n (KJbz n)`, uniformly in `h`: the box contains all the jet data (the
radicand jets are bounded by `KJbz n` and the derivatives of `h` by `1/100`), and the radicand
entries stay in `[1/100, 10]`, so that the two component functions are `C^∞` on the open
neighbourhood `KJopen n` of the box. -/

/-- The `(Zrad, lineSlope)` jet block at the first chord endpoint `t₁ = -z₀`, read off from the
kernel jet `v : KJIx n → ℝ`. -/
def fedKJblk1 (n : ℕ) (v : KJIx n → ℝ) : Fin (n + 1) × Bool → ℝ
  | (j, false) => KJZ1 n v j.1
  | (j, true) => if j.1 = 0 then v KJIx.t1 + KJW n v 0 else KJW n v j.1

/-- The `(Zrad, lineSlope)` jet block at the second chord endpoint `t₂ = z₁`. -/
def fedKJblk2 (n : ℕ) (v : KJIx n → ℝ) : Fin (n + 1) × Bool → ℝ
  | (j, false) => KJZ2 n v j.1
  | (j, true) => if j.1 = 0 then v KJIx.t2 + KJW n v 0 else KJW n v j.1

@[simp] lemma fedKJblk1_false (n : ℕ) (v : KJIx n → ℝ) (j : Fin (n + 1)) :
    fedKJblk1 n v (j, false) = KJZ1 n v j.1 := rfl
@[simp] lemma fedKJblk1_true (n : ℕ) (v : KJIx n → ℝ) (j : Fin (n + 1)) :
    fedKJblk1 n v (j, true) = if j.1 = 0 then v KJIx.t1 + KJW n v 0 else KJW n v j.1 := rfl
@[simp] lemma fedKJblk2_false (n : ℕ) (v : KJIx n → ℝ) (j : Fin (n + 1)) :
    fedKJblk2 n v (j, false) = KJZ2 n v j.1 := rfl
@[simp] lemma fedKJblk2_true (n : ℕ) (v : KJIx n → ℝ) (j : Fin (n + 1)) :
    fedKJblk2 n v (j, true) = if j.1 = 0 then v KJIx.t2 + KJW n v 0 else KJW n v j.1 := rfl

/-- **The second component of the kernel vector as a function of the jet.**  Together with `KF1`
(`KvecDefs`), this exhibits the whole vector `KvecM n h a σ z` as the value at the jet
`KJet n h σ z a` of a function of the jet which does not depend on `h`, `a`, `σ` or `z`. -/
noncomputable def fedPhi2 (n : ℕ) (v : KJIx n → ℝ) : ℝ :=
  -((Qaux.Q ((n : ℝ) - 1 / 2) n (fedKJblk1 n v)) / Real.sqrt (v KJIx.kd1) * v KJIx.c2 +
    (Qaux.Q ((n : ℝ) - 1 / 2) n (fedKJblk2 n v)) / Real.sqrt (v KJIx.kd2) * v KJIx.c3)

/-! ## Smoothness of `fedPhi2` on the region where both radicands are positive -/

lemma fed_contDiff_KJblk1 (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => fedKJblk1 n v) := by
  rw [contDiff_pi]
  intro p
  obtain ⟨j, b⟩ := p
  cases b
  · have hfun : (fun v : KJIx n → ℝ => fedKJblk1 n v (j, false))
        = fun v : KJIx n → ℝ => v (.Z1 (⟨j.1, by have := j.2; omega⟩ : Fin (n + 2))) := by
      funext v; simpa using KJZ1_eq n v ⟨j.1, by have := j.2; omega⟩
    rw [hfun]
    exact contDiff_apply ℝ ℝ _
  · by_cases h0 : j.1 = 0
    · have hfun : (fun v : KJIx n → ℝ => fedKJblk1 n v (j, true))
          = fun v : KJIx n → ℝ => v KJIx.t1 + KJW n v 0 := by
        funext v; rw [fedKJblk1_true, if_pos h0]
      rw [hfun]
      exact (contDiff_apply ℝ ℝ KJIx.t1).add (KvecJet_contDiff_KJW n 0)
    · have hfun : (fun v : KJIx n → ℝ => fedKJblk1 n v (j, true))
          = fun v : KJIx n → ℝ => KJW n v j.1 := by
        funext v; rw [fedKJblk1_true, if_neg h0]
      rw [hfun]
      exact KvecJet_contDiff_KJW n j.1

lemma fed_contDiff_KJblk2 (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => fedKJblk2 n v) := by
  rw [contDiff_pi]
  intro p
  obtain ⟨j, b⟩ := p
  cases b
  · have hfun : (fun v : KJIx n → ℝ => fedKJblk2 n v (j, false))
        = fun v : KJIx n → ℝ => v (.Z2 (⟨j.1, by have := j.2; omega⟩ : Fin (n + 2))) := by
      funext v; simpa using KJZ2_eq n v ⟨j.1, by have := j.2; omega⟩
    rw [hfun]
    exact contDiff_apply ℝ ℝ _
  · by_cases h0 : j.1 = 0
    · have hfun : (fun v : KJIx n → ℝ => fedKJblk2 n v (j, true))
          = fun v : KJIx n → ℝ => v KJIx.t2 + KJW n v 0 := by
        funext v; rw [fedKJblk2_true, if_pos h0]
      rw [hfun]
      exact (contDiff_apply ℝ ℝ KJIx.t2).add (KvecJet_contDiff_KJW n 0)
    · have hfun : (fun v : KJIx n → ℝ => fedKJblk2 n v (j, true))
          = fun v : KJIx n → ℝ => KJW n v j.1 := by
        funext v; rw [fedKJblk2_true, if_neg h0]
      rw [hfun]
      exact KvecJet_contDiff_KJW n j.1

/-- `fedPhi2` is `C^∞` on the set where both radicands are non-zero. -/
theorem fed_contDiffOn_Phi2 (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => fedPhi2 n v) (KJopen n) := by
  have hgoal : (fun v : KJIx n → ℝ => fedPhi2 n v) = fun v : KJIx n → ℝ =>
      -((Qaux.Q ((n : ℝ) - 1 / 2) n (fedKJblk1 n v)) / Real.sqrt (v KJIx.kd1) * v KJIx.c2 +
        (Qaux.Q ((n : ℝ) - 1 / 2) n (fedKJblk2 n v)) / Real.sqrt (v KJIx.kd2) * v KJIx.c3) := by
    funext v; rfl
  rw [hgoal]
  have hQ1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => Qaux.Q ((n : ℝ) - 1 / 2) n (fedKJblk1 n v)) (KJopen n) :=
    ((Qaux.contDiff_Q ((n : ℝ) - 1 / 2) n).comp (fed_contDiff_KJblk1 n)).contDiffOn
  have hQ2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => Qaux.Q ((n : ℝ) - 1 / 2) n (fedKJblk2 n v)) (KJopen n) :=
    ((Qaux.contDiff_Q ((n : ℝ) - 1 / 2) n).comp (fed_contDiff_KJblk2 n)).contDiffOn
  have hK1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => (Qaux.Q ((n : ℝ) - 1 / 2) n (fedKJblk1 n v)) / Real.sqrt (v KJIx.kd1))
      (KJopen n) := by
    refine ContDiffOn.div hQ1 ?_ ?_
    · exact ContDiffOn.sqrt ((contDiff_apply ℝ ℝ KJIx.kd1).contDiffOn)
        (fun v hv => ne_of_gt hv.1)
    · intro v hv; exact ne_of_gt (Real.sqrt_pos_of_pos hv.1)
  have hK2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => (Qaux.Q ((n : ℝ) - 1 / 2) n (fedKJblk2 n v)) / Real.sqrt (v KJIx.kd2))
      (KJopen n) := by
    refine ContDiffOn.div hQ2 ?_ ?_
    · exact ContDiffOn.sqrt ((contDiff_apply ℝ ℝ KJIx.kd2).contDiffOn)
        (fun v hv => ne_of_gt hv.2)
    · intro v hv; exact ne_of_gt (Real.sqrt_pos_of_pos hv.2)
  exact ContDiffOn.neg (ContDiffOn.add
    (ContDiffOn.mul hK1 (contDiff_apply ℝ ℝ KJIx.c2).contDiffOn)
    (ContDiffOn.mul hK2 (contDiff_apply ℝ ℝ KJIx.c3).contDiffOn))

/-! ## The jet of `(Zrad, lineSlope)` read off from `KJet` -/

/-- For `m ≥ 1`, the `m`-th derivative of `v ↦ lineSlope h v t` is the `(m+1)`-st derivative
of `h`. -/
lemma fed_iteratedDeriv_lineSlope_ge_one (h : ℝ → ℝ) (u t : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    iteratedDeriv m (fun v : ℝ => lineSlope h v t) u = iteratedDeriv (m + 1) h u := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h1 : (fun v : ℝ => lineSlope h v t) = fun v : ℝ => t + deriv h v := by
    funext v; rfl
  rw [h1, iteratedDeriv_succ_add_const m' t (deriv h) u]
  exact (congrFun (iteratedDeriv_succ' (n := m' + 1) (f := h)) u).symm

/-- The jet block of the pair `(Zrad h (·,σ,-z₀), lineSlope h (·,-z₀))` is read off from the
kernel jet `KJet` at the first chord endpoint. -/
lemma fedKJblk1_KJet (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) (u : ℝ) :
    fedKJblk1 n (KJet n h σ z u)
      = Qaux.Jjet h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) σ (-(z 0)) n u := by
  funext p
  obtain ⟨j, b⟩ := p
  cases b
  · rw [fedKJblk1_false, Qaux.Jjet_false]
    show KJZ1 n (KJet n h σ z u) j.1
      = iteratedDeriv j.1 (Qaux.Zsec h σ (-(z 0))) u
    rw [KJZ1_eq n (KJet n h σ z u) ⟨j.1, by have := j.2; omega⟩, KJet_Z1]
    exact kjet_eq_Zrad (hh.of_le (by norm_num)) σ (-(z 0)) u j.1
  · rw [fedKJblk1_true]
    have hfun : (fun x : ℝ => (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) (x, σ, -(z 0)))
        = fun x : ℝ => lineSlope h x (-(z 0)) := by
      funext x; rfl
    rw [Qaux.Jjet_true, hfun]
    rcases Nat.eq_zero_or_pos j.1 with hj0 | hjpos
    · rw [if_pos hj0]
      have hR : iteratedDeriv j.1 (fun x : ℝ => lineSlope h x (-(z 0))) u
          = -(z 0) + deriv h u := by
        rw [hj0, iteratedDeriv_zero]
        rfl
      rw [hR, KJet_t1, KJW_of_lt n (KJet n h σ z u) (by omega : 0 < n + 1), KJet_w,
        iteratedDeriv_one]
    · rw [if_neg (by omega : ¬ j.1 = 0),
        fed_iteratedDeriv_lineSlope_ge_one h u (-(z 0)) hjpos,
        KJW_of_lt n (KJet n h σ z u) (by have := j.2; omega), KJet_w]

/-- The jet block of the pair `(Zrad h (·,σ,z₁), lineSlope h (·,z₁))` is read off from the kernel
jet `KJet` at the second chord endpoint. -/
lemma fedKJblk2_KJet (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) (u : ℝ) :
    fedKJblk2 n (KJet n h σ z u)
      = Qaux.Jjet h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) σ (z 1) n u := by
  funext p
  obtain ⟨j, b⟩ := p
  cases b
  · rw [fedKJblk2_false, Qaux.Jjet_false]
    show KJZ2 n (KJet n h σ z u) j.1
      = iteratedDeriv j.1 (Qaux.Zsec h σ (z 1)) u
    rw [KJZ2_eq n (KJet n h σ z u) ⟨j.1, by have := j.2; omega⟩, KJet_Z2]
    exact kjet_eq_Zrad (hh.of_le (by norm_num)) σ (z 1) u j.1
  · rw [fedKJblk2_true]
    have hfun : (fun x : ℝ => (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) (x, σ, z 1))
        = fun x : ℝ => lineSlope h x (z 1) := by
      funext x; rfl
    rw [Qaux.Jjet_true, hfun]
    rcases Nat.eq_zero_or_pos j.1 with hj0 | hjpos
    · rw [if_pos hj0]
      have hR : iteratedDeriv j.1 (fun x : ℝ => lineSlope h x (z 1)) u
          = z 1 + deriv h u := by
        rw [hj0, iteratedDeriv_zero]
        rfl
      rw [hR, KJet_t2, KJW_of_lt n (KJet n h σ z u) (by omega : 0 < n + 1), KJet_w,
        iteratedDeriv_one]
    · rw [if_neg (by omega : ¬ j.1 = 0),
        fed_iteratedDeriv_lineSlope_ge_one h u (z 1) hjpos,
        KJW_of_lt n (KJet n h σ z u) (by have := j.2; omega), KJet_w]

/-! ## The two rows of `KvecM` as functions of the jet -/

/-- The manifest second numerator is the jet recursion `Q` applied to the jet of the pair
`(Zrad h (·,σ,t), lineSlope h (·,t))`, for **every** `a σ t`. -/
theorem fedK2M_eq_Q (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ t : ℝ) :
    KernelExt.K2M n h a σ t =
      Qaux.Q ((n : ℝ) - 1 / 2) n
        (Qaux.Jjet h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) σ t n a)
        / Real.sqrt (krad h σ t a) := by
  have hinit : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) := by
    unfold lineSlope; fun_prop
  rw [KernelExt.K2M, KernelExt.J2M,
    Qaux.Rnu_eq_Q ((n : ℝ) - 1 / 2) hh hinit n a σ t]
  rfl

/-- **First row of `KvecM` as a function of the jet**, at every `a`. -/
lemma fedKvecM_row0 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ : ℝ) (z : St) :
    (KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) 0 = KF1 n (KJet n h σ z a) := by
  have h1 : (KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) 0
      = -(KernelExt.K1M n h a σ (-(z 0)) * z 2 + KernelExt.K1M n h a σ (z 1) * z 3) := by
    simp only [KernelExt.KvecM, Matrix.cons_val_zero]
  rw [h1, K1M_eq_k1ext n hh a σ (-(z 0)), K1M_eq_k1ext n hh a σ (z 1)]
  simp only [KF1, KJet_aa, KJet_c2, KJet_c3, KJet_kd1, KJet_kd2]
  rw [← KJk1_KJet_eq n h σ z a, ← KJk1_KJet_eq2 n h σ z a]

/-- **Second row of `KvecM` as a function of the jet**, at every `a`. -/
lemma fedKvecM_row1 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ : ℝ) (z : St) :
    (KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) 1 = fedPhi2 n (KJet n h σ z a) := by
  have h1 : (KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) 1
      = -(KernelExt.K2M n h a σ (-(z 0)) * z 2 + KernelExt.K2M n h a σ (z 1) * z 3) := by
    simp only [KernelExt.KvecM, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h1, fedK2M_eq_Q n hh a σ (-(z 0)), fedK2M_eq_Q n hh a σ (z 1)]
  rw [fedPhi2, fedKJblk1_KJet n hh σ z a, fedKJblk2_KJet n hh σ z a]
  simp only [KJet_kd1, KJet_kd2, KJet_c2, KJet_c3]

/-- The kernel vector as a function of the jet, both rows at once. -/
def fedKJrow (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) : Fin 2 → ℝ :=
  ![KF1 n (KJet n h σ z u), fedPhi2 n (KJet n h σ z u)]

@[simp] lemma fedKJrow_zero (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    fedKJrow n h σ z u 0 = KF1 n (KJet n h σ z u) := rfl
@[simp] lemma fedKJrow_one (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    fedKJrow n h σ z u 1 = fedPhi2 n (KJet n h σ z u) := rfl

/-- The two indices of `Fin 2`. -/
lemma fed_fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

/-- The four indices of `Fin 4`. -/
lemma fed_fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp

/-- **The whole kernel vector is a fixed function of the jet**, at every `a`. -/
lemma fedKvecM_eq_row (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) :
    (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) = fedKJrow n h σ z := by
  funext u i
  rcases fed_fin2_cases i with h | h
  · rw [h]; exact fedKvecM_row0 n hh u σ z
  · rw [h]; exact fedKvecM_row1 n hh u σ z

end

end Work.OddVolterra.Window

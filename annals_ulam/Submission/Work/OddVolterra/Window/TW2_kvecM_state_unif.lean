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
def KJblk1 (n : ℕ) (v : KJIx n → ℝ) : Fin (n + 1) × Bool → ℝ
  | (j, false) => KJZ1 n v j.1
  | (j, true) => if j.1 = 0 then v KJIx.t1 + KJW n v 0 else KJW n v j.1

/-- The `(Zrad, lineSlope)` jet block at the second chord endpoint `t₂ = z₁`. -/
def KJblk2 (n : ℕ) (v : KJIx n → ℝ) : Fin (n + 1) × Bool → ℝ
  | (j, false) => KJZ2 n v j.1
  | (j, true) => if j.1 = 0 then v KJIx.t2 + KJW n v 0 else KJW n v j.1

@[simp] lemma KJblk1_false (n : ℕ) (v : KJIx n → ℝ) (j : Fin (n + 1)) :
    KJblk1 n v (j, false) = KJZ1 n v j.1 := rfl
@[simp] lemma KJblk1_true (n : ℕ) (v : KJIx n → ℝ) (j : Fin (n + 1)) :
    KJblk1 n v (j, true) = if j.1 = 0 then v KJIx.t1 + KJW n v 0 else KJW n v j.1 := rfl
@[simp] lemma KJblk2_false (n : ℕ) (v : KJIx n → ℝ) (j : Fin (n + 1)) :
    KJblk2 n v (j, false) = KJZ2 n v j.1 := rfl
@[simp] lemma KJblk2_true (n : ℕ) (v : KJIx n → ℝ) (j : Fin (n + 1)) :
    KJblk2 n v (j, true) = if j.1 = 0 then v KJIx.t2 + KJW n v 0 else KJW n v j.1 := rfl

/-- **The second component of the kernel vector as a function of the jet.**  Together with `KF1`
(`KvecDefs`), this exhibits the whole vector `KvecM n h a σ z` as the value at the jet
`KJet n h σ z a` of a function of the jet which does not depend on `h`, `a`, `σ` or `z`. -/
noncomputable def Phi2 (n : ℕ) (v : KJIx n → ℝ) : ℝ :=
  -((Qaux.Q ((n : ℝ) - 1 / 2) n (KJblk1 n v)) / Real.sqrt (v KJIx.kd1) * v KJIx.c2 +
    (Qaux.Q ((n : ℝ) - 1 / 2) n (KJblk2 n v)) / Real.sqrt (v KJIx.kd2) * v KJIx.c3)

/-! ## Smoothness of `Phi2` on the region where both radicands are positive -/

lemma contDiff_KJblk1 (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KJblk1 n v) := by
  rw [contDiff_pi]
  intro p
  obtain ⟨j, b⟩ := p
  cases b
  · have hfun : (fun v : KJIx n → ℝ => KJblk1 n v (j, false))
        = fun v : KJIx n → ℝ => v (.Z1 (⟨j.1, by have := j.2; omega⟩ : Fin (n + 2))) := by
      funext v; simpa using KJZ1_eq n v ⟨j.1, by have := j.2; omega⟩
    rw [hfun]
    exact contDiff_apply ℝ ℝ _
  · by_cases h0 : j.1 = 0
    · have hfun : (fun v : KJIx n → ℝ => KJblk1 n v (j, true))
          = fun v : KJIx n → ℝ => v KJIx.t1 + KJW n v 0 := by
        funext v; rw [KJblk1_true, if_pos h0]
      rw [hfun]
      exact (contDiff_apply ℝ ℝ KJIx.t1).add (KvecJet_contDiff_KJW n 0)
    · have hfun : (fun v : KJIx n → ℝ => KJblk1 n v (j, true))
          = fun v : KJIx n → ℝ => KJW n v j.1 := by
        funext v; rw [KJblk1_true, if_neg h0]
      rw [hfun]
      exact KvecJet_contDiff_KJW n j.1

lemma contDiff_KJblk2 (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KJblk2 n v) := by
  rw [contDiff_pi]
  intro p
  obtain ⟨j, b⟩ := p
  cases b
  · have hfun : (fun v : KJIx n → ℝ => KJblk2 n v (j, false))
        = fun v : KJIx n → ℝ => v (.Z2 (⟨j.1, by have := j.2; omega⟩ : Fin (n + 2))) := by
      funext v; simpa using KJZ2_eq n v ⟨j.1, by have := j.2; omega⟩
    rw [hfun]
    exact contDiff_apply ℝ ℝ _
  · by_cases h0 : j.1 = 0
    · have hfun : (fun v : KJIx n → ℝ => KJblk2 n v (j, true))
          = fun v : KJIx n → ℝ => v KJIx.t2 + KJW n v 0 := by
        funext v; rw [KJblk2_true, if_pos h0]
      rw [hfun]
      exact (contDiff_apply ℝ ℝ KJIx.t2).add (KvecJet_contDiff_KJW n 0)
    · have hfun : (fun v : KJIx n → ℝ => KJblk2 n v (j, true))
          = fun v : KJIx n → ℝ => KJW n v j.1 := by
        funext v; rw [KJblk2_true, if_neg h0]
      rw [hfun]
      exact KvecJet_contDiff_KJW n j.1

/-- `Phi2` is `C^∞` on the set where both radicands are non-zero. -/
theorem contDiffOn_Phi2 (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => Phi2 n v) (KJopen n) := by
  have hgoal : (fun v : KJIx n → ℝ => Phi2 n v) = fun v : KJIx n → ℝ =>
      -((Qaux.Q ((n : ℝ) - 1 / 2) n (KJblk1 n v)) / Real.sqrt (v KJIx.kd1) * v KJIx.c2 +
        (Qaux.Q ((n : ℝ) - 1 / 2) n (KJblk2 n v)) / Real.sqrt (v KJIx.kd2) * v KJIx.c3) := by
    funext v; rfl
  rw [hgoal]
  have hQ1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => Qaux.Q ((n : ℝ) - 1 / 2) n (KJblk1 n v)) (KJopen n) :=
    ((Qaux.contDiff_Q ((n : ℝ) - 1 / 2) n).comp (contDiff_KJblk1 n)).contDiffOn
  have hQ2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => Qaux.Q ((n : ℝ) - 1 / 2) n (KJblk2 n v)) (KJopen n) :=
    ((Qaux.contDiff_Q ((n : ℝ) - 1 / 2) n).comp (contDiff_KJblk2 n)).contDiffOn
  have hK1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => (Qaux.Q ((n : ℝ) - 1 / 2) n (KJblk1 n v)) / Real.sqrt (v KJIx.kd1))
      (KJopen n) := by
    refine ContDiffOn.div hQ1 ?_ ?_
    · exact ContDiffOn.sqrt ((contDiff_apply ℝ ℝ KJIx.kd1).contDiffOn)
        (fun v hv => ne_of_gt hv.1)
    · intro v hv; exact ne_of_gt (Real.sqrt_pos_of_pos hv.1)
  have hK2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => (Qaux.Q ((n : ℝ) - 1 / 2) n (KJblk2 n v)) / Real.sqrt (v KJIx.kd2))
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
lemma iteratedDeriv_lineSlope_ge_one (h : ℝ → ℝ) (u t : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    iteratedDeriv m (fun v : ℝ => lineSlope h v t) u = iteratedDeriv (m + 1) h u := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h1 : (fun v : ℝ => lineSlope h v t) = fun v : ℝ => t + deriv h v := by
    funext v; rfl
  rw [h1, iteratedDeriv_succ_add_const m' t (deriv h) u]
  exact (congrFun (iteratedDeriv_succ' (n := m' + 1) (f := h)) u).symm

/-- The jet block of the pair `(Zrad h (·,σ,-z₀), lineSlope h (·,-z₀))` is read off from the
kernel jet `KJet` at the first chord endpoint. -/
lemma KJblk1_KJet (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) (u : ℝ) :
    KJblk1 n (KJet n h σ z u)
      = Qaux.Jjet h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) σ (-(z 0)) n u := by
  funext p
  obtain ⟨j, b⟩ := p
  cases b
  · rw [KJblk1_false, Qaux.Jjet_false]
    show KJZ1 n (KJet n h σ z u) j.1
      = iteratedDeriv j.1 (Qaux.Zsec h σ (-(z 0))) u
    rw [KJZ1_eq n (KJet n h σ z u) ⟨j.1, by have := j.2; omega⟩, KJet_Z1]
    exact kjet_eq_Zrad (hh.of_le (by norm_num)) σ (-(z 0)) u j.1
  · rw [KJblk1_true]
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
        iteratedDeriv_lineSlope_ge_one h u (-(z 0)) hjpos,
        KJW_of_lt n (KJet n h σ z u) (by have := j.2; omega), KJet_w]

/-- The jet block of the pair `(Zrad h (·,σ,z₁), lineSlope h (·,z₁))` is read off from the kernel
jet `KJet` at the second chord endpoint. -/
lemma KJblk2_KJet (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) (u : ℝ) :
    KJblk2 n (KJet n h σ z u)
      = Qaux.Jjet h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) σ (z 1) n u := by
  funext p
  obtain ⟨j, b⟩ := p
  cases b
  · rw [KJblk2_false, Qaux.Jjet_false]
    show KJZ2 n (KJet n h σ z u) j.1
      = iteratedDeriv j.1 (Qaux.Zsec h σ (z 1)) u
    rw [KJZ2_eq n (KJet n h σ z u) ⟨j.1, by have := j.2; omega⟩, KJet_Z2]
    exact kjet_eq_Zrad (hh.of_le (by norm_num)) σ (z 1) u j.1
  · rw [KJblk2_true]
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
        iteratedDeriv_lineSlope_ge_one h u (z 1) hjpos,
        KJW_of_lt n (KJet n h σ z u) (by have := j.2; omega), KJet_w]

/-! ## The two rows of `KvecM` as functions of the jet -/

/-- The manifest second numerator is the jet recursion `Q` applied to the jet of the pair
`(Zrad h (·,σ,t), lineSlope h (·,t))`, for **every** `a σ t`. -/
theorem K2M_eq_Q (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ t : ℝ) :
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
lemma KvecM_row0 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ : ℝ) (z : St) :
    (KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) 0 = KF1 n (KJet n h σ z a) := by
  have h1 : (KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) 0
      = -(KernelExt.K1M n h a σ (-(z 0)) * z 2 + KernelExt.K1M n h a σ (z 1) * z 3) := by
    simp only [KernelExt.KvecM, Matrix.cons_val_zero]
  rw [h1, K1M_eq_k1ext n hh a σ (-(z 0)), K1M_eq_k1ext n hh a σ (z 1)]
  simp only [KF1, KJet_aa, KJet_c2, KJet_c3, KJet_kd1, KJet_kd2]
  rw [← KJk1_KJet_eq n h σ z a, ← KJk1_KJet_eq2 n h σ z a]

/-- **Second row of `KvecM` as a function of the jet**, at every `a`. -/
lemma KvecM_row1 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ : ℝ) (z : St) :
    (KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) 1 = Phi2 n (KJet n h σ z a) := by
  have h1 : (KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) 1
      = -(KernelExt.K2M n h a σ (-(z 0)) * z 2 + KernelExt.K2M n h a σ (z 1) * z 3) := by
    simp only [KernelExt.KvecM, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h1, K2M_eq_Q n hh a σ (-(z 0)), K2M_eq_Q n hh a σ (z 1)]
  rw [Phi2, KJblk1_KJet n hh σ z a, KJblk2_KJet n hh σ z a]
  simp only [KJet_kd1, KJet_kd2, KJet_c2, KJet_c3]

/-- The kernel vector as a function of the jet, both rows at once. -/
def KJrow (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) : Fin 2 → ℝ :=
  ![KF1 n (KJet n h σ z u), Phi2 n (KJet n h σ z u)]

@[simp] lemma KJrow_zero (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJrow n h σ z u 0 = KF1 n (KJet n h σ z u) := rfl
@[simp] lemma KJrow_one (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJrow n h σ z u 1 = Phi2 n (KJet n h σ z u) := rfl

/-- The two indices of `Fin 2`. -/
lemma fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

/-- The four indices of `Fin 4`. -/
lemma fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp

/-- **The whole kernel vector is a fixed function of the jet**, at every `a`. -/
lemma KvecM_eq_row (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) :
    (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) = KJrow n h σ z := by
  funext u i
  rcases fin2_cases i with h | h
  · rw [h]; exact KvecM_row0 n hh u σ z
  · rw [h]; exact KvecM_row1 n hh u σ z

/-! ## State data of the ball of radius `9/20` -/

/-- On the ball of radius `9/20` around `baseState σ` (`σ` in the window) the first two state
coordinates are at least `1/4` and all coordinates are at most `2` in absolute value. -/
lemma tw2_ball_data {σ : ℝ} (hσ : σ ∈ Set.Icc wLeft wRight) {z : St}
    (hz : z ∈ Metric.closedBall (baseState σ) (9 / 20)) :
    1 / 4 ≤ z 0 ∧ 1 / 4 ≤ z 1 ∧ ∀ i : Fin 4, |z i| ≤ 2 := by
  have hcoord : ∀ i : Fin 4, |z i - baseState σ i| ≤ 9 / 20 := by
    intro i
    have h := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h (Metric.mem_closedBall.mp hz)
  have hbase : ∀ i : Fin 4, |baseState σ i| ≤ 1 := by
    intro i
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · simpa [Work.OddVolterra.baseState] using Commons.Geometry.Ulam.abs_profileX_le_one σ
    · simpa [Work.OddVolterra.baseState] using Commons.Geometry.Ulam.abs_profileX_le_one σ
    · have hpd : |deriv Commons.Geometry.Ulam.profileX σ| ≤ 1 := by
        linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]
      simpa [Work.OddVolterra.baseState] using hpd
    · have hpd : |deriv Commons.Geometry.Ulam.profileX σ| ≤ 1 := by
        linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]
      simpa [Work.OddVolterra.baseState] using hpd
  have hσ7 : (7 / 10 : ℝ) ≤ σ := by have h := hσ.1; rw [wLeft] at h; exact h
  have hσ1 : σ ≤ 1 := by have h := hσ.2; rw [wRight] at h; linarith
  have hprof : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX σ :=
    seven_tenths_le_profileX (by linarith) hσ1
  refine ⟨?_, ?_, fun i => ?_⟩
  · have h0 := hcoord 0
    have hb : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := by
      simp [Work.OddVolterra.baseState]
    rw [hb] at h0
    linarith [(abs_le.mp h0).1]
  · have h1 := hcoord 1
    have hb : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := by
      simp [Work.OddVolterra.baseState]
    rw [hb] at h1
    linarith [(abs_le.mp h1).1]
  · calc |z i| = |(z i - baseState σ i) + baseState σ i| := by ring_nf
      _ ≤ |z i - baseState σ i| + |baseState σ i| := abs_add_le _ _
      _ ≤ 9 / 20 + 1 := add_le_add (hcoord i) (hbase i)
      _ ≤ 2 := by norm_num

/-! ## The uniform bound and state-Lipschitz constant

The assembly is compactness: `KvecM n h a σ z = KJrow n h σ z a` at *every* `a` (the row
identities above), `JetCurve_box` gives the uniform value/derivative/Lipschitz bounds for the two
components `KF1`, `Phi2` of `KJrow` on the compact box `KJbox n (KJbz n)`, and the jet curve
`u ↦ KJet n h σ z u` is `KJbz n`-bounded with `u`-derivative and `Kj`-Lipschitz in the state
(`KJet_mem_box_deriv`, `KJet_state_lipschitz_window`). -/

theorem TW2_kvecM_state_unif (n : ℕ) (hn : 1 ≤ n) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ Work.OddVolterra.Window.KvecMStateData n M C := by
  have _ : 1 ≤ n := hn
  obtain ⟨Kj, hKjnn, hKj⟩ := KJet_state_lipschitz_window n
  obtain ⟨C1, hC1nn, hC1⟩ := JetCurve_box (E := KJIx n → ℝ) (fun v => KF1 n v) (isOpen_KJopen n)
    (convex_KJbox n (KJbz n)) (isCompact_KJbox n (KJbz n)) (KJbox_subset_KJopen n (KJbz n))
    (KvecJet_smooth n).1 (KJbz_nonneg n)
  obtain ⟨C2, hC2nn, hC2⟩ := JetCurve_box (E := KJIx n → ℝ) (fun v => Phi2 n v) (isOpen_KJopen n)
    (convex_KJbox n (KJbz n)) (isCompact_KJbox n (KJbz n)) (KJbox_subset_KJopen n (KJbz n))
    (contDiffOn_Phi2 n) (KJbz_nonneg n)
  have hCn : 0 ≤ max C1 C2 := le_max_of_le_left hC1nn
  have hKF1diff : ∀ v ∈ KJbox n (KJbz n), DifferentiableAt ℝ (fun v : KJIx n → ℝ => KF1 n v) v :=
    fun v hv => ((KvecJet_smooth n).1.contDiffAt ((isOpen_KJopen n).mem_nhds
      (KJbox_subset_KJopen n (KJbz n) hv))).differentiableAt (by simp)
  have hPhi2diff : ∀ v ∈ KJbox n (KJbz n),
      DifferentiableAt ℝ (fun v : KJIx n → ℝ => Phi2 n v) v :=
    fun v hv => ((contDiffOn_Phi2 n).contDiffAt ((isOpen_KJopen n).mem_nhds
      (KJbox_subset_KJopen n (KJbz n) hv))).differentiableAt (by simp)
  refine ⟨max C1 C2 * Kj, max C1 C2, by positivity, hCn, ?_⟩
  intro h hh hsupp hjet a ha σ hσ z hz z' hz'
  -- ## the state data of the two points
  obtain ⟨hz0, hz1, hz2⟩ := tw2_ball_data hσ hz
  obtain ⟨hz'0, hz'1, hz'2⟩ := tw2_ball_data hσ hz'
  -- ## the window data
  have hσw : σ ∈ Set.Icc (7 / 10 : ℝ) (19 / 20) := hσ
  have haw : a ∈ Set.Icc (7 / 10 : ℝ) (19 / 20) := ha
  have hσ9 : σ ∈ Set.Icc (7 / 10 : ℝ) 1 := by
    refine ⟨hσ.1, ?_⟩
    have h := hσ.2; rw [wRight] at h; linarith
  have ha9 : a ∈ Set.Icc (9 / 20 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have h := ha.1; rw [wLeft] at h; linarith
    · have h := ha.2; rw [wRight] at h; linarith
  -- ## the jet data, for an arbitrary state of the ball
  have jetdata : ∀ w : St, (1 / 4 ≤ w 0) → (1 / 4 ≤ w 1) → (∀ i : Fin 4, |w i| ≤ 2) →
      KJet n h σ w a ∈ KJbox n (KJbz n) ∧
      ‖deriv (fun u : ℝ => KJet n h σ w u) a‖ ≤ KJbz n := by
    intro w hw0 hw1 hw
    have hw0pos : (0 : ℝ) < w 0 := by linarith
    have hw1pos : (0 : ℝ) < w 1 := by linarith
    obtain ⟨hk1, hk1', hk1d⟩ := krad_window_data hh hjet hσw haw
      (by rw [abs_neg, abs_of_pos hw0pos]; linarith)
      (by rw [abs_neg, abs_of_pos hw0pos]; linarith [(abs_le.mp (hw 0)).2])
    obtain ⟨hk2, hk2', hk2d⟩ := krad_window_data hh hjet hσw haw
      (by rw [abs_of_pos hw1pos]; linarith)
      (by rw [abs_of_pos hw1pos]; linarith [(abs_le.mp (hw 1)).2])
    exact KJet_mem_box_deriv n hh hjet hσw hw0 hw1 hw haw hk1 hk1' hk2 hk2' hk1d hk2d
  obtain ⟨hmemZ, hderZ⟩ := jetdata z hz0 hz1 hz2
  obtain ⟨hmemZ', hderZ'⟩ := jetdata z' hz'0 hz'1 hz'2
  -- ## the jet curves and their state-Lipschitz data
  have hcdZ : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z u) := contDiff_KJet_local n hh σ z
  have hcdZ' : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z' u) :=
    contDiff_KJet_local n hh σ z'
  have hlip := hKj h hh hjet σ hσ9 a ha9 z z' (by linarith) (by linarith) hz2
    (by linarith) (by linarith) hz'2
  have hδnn : 0 ≤ Kj * ‖z - z'‖ := mul_nonneg hKjnn (norm_nonneg _)
  -- ## `JetCurve_box` for the two components of the jet vector
  have hJ1 := hC1 (fun u : ℝ => KJet n h σ z u) (fun u : ℝ => KJet n h σ z' u) a
    (Kj * ‖z - z'‖) hδnn hcdZ hcdZ' hmemZ hmemZ' hderZ hderZ' hlip.1 hlip.2
  have hJ2 := hC2 (fun u : ℝ => KJet n h σ z u) (fun u : ℝ => KJet n h σ z' u) a
    (Kj * ‖z - z'‖) hδnn hcdZ hcdZ' hmemZ hmemZ' hderZ hderZ' hlip.1 hlip.2
  obtain ⟨hA1, -, hE1, -, hG1, hH1⟩ := hJ1
  obtain ⟨hA2, -, hE2, -, hG2, hH2⟩ := hJ2
  -- ## constants
  have hC1le : C1 ≤ max C1 C2 := le_max_left _ _
  have hC2le : C2 ≤ max C1 C2 := le_max_right _ _
  have hM1 : C1 * (Kj * ‖z - z'‖) ≤ (max C1 C2 * Kj) * ‖z - z'‖ := by
    calc C1 * (Kj * ‖z - z'‖) = (C1 * Kj) * ‖z - z'‖ := by ring
      _ ≤ (max C1 C2 * Kj) * ‖z - z'‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1le hKjnn) (norm_nonneg _)
  have hM2 : C2 * (Kj * ‖z - z'‖) ≤ (max C1 C2 * Kj) * ‖z - z'‖ := by
    calc C2 * (Kj * ‖z - z'‖) = (C2 * Kj) * ‖z - z'‖ := by ring
      _ ≤ (max C1 C2 * Kj) * ‖z - z'‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le hKjnn) (norm_nonneg _)
  -- ## differentiability of the two rows along the two jet curves
  have hdiffZ : ∀ i : Fin 2, DifferentiableAt ℝ (fun u : ℝ => KJrow n h σ z u i) a := by
    intro i
    rcases fin2_cases i with h0 | h1
    · rw [h0]
      exact (hKF1diff _ hmemZ).comp a ((hcdZ.differentiable (by simp)).differentiableAt)
    · rw [h1]
      exact (hPhi2diff _ hmemZ).comp a ((hcdZ.differentiable (by simp)).differentiableAt)
  have hdiffZ' : ∀ i : Fin 2, DifferentiableAt ℝ (fun u : ℝ => KJrow n h σ z' u i) a := by
    intro i
    rcases fin2_cases i with h0 | h1
    · rw [h0]
      exact (hKF1diff _ hmemZ').comp a ((hcdZ'.differentiable (by simp)).differentiableAt)
    · rw [h1]
      exact (hPhi2diff _ hmemZ').comp a ((hcdZ'.differentiable (by simp)).differentiableAt)
  have hderZrow : deriv (fun u : ℝ => KJrow n h σ z u) a
      = fun i => deriv (fun u : ℝ => KJrow n h σ z u i) a :=
    deriv_pi (𝕜 := ℝ) (x := a) (φ := fun u : ℝ => KJrow n h σ z u) hdiffZ
  have hderZ'row : deriv (fun u : ℝ => KJrow n h σ z' u) a
      = fun i => deriv (fun u : ℝ => KJrow n h σ z' u i) a :=
    deriv_pi (𝕜 := ℝ) (x := a) (φ := fun u : ℝ => KJrow n h σ z' u) hdiffZ'
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the value bound
    rw [pi_norm_le_iff_of_nonneg hCn]
    intro i
    rcases fin2_cases i with h0 | h1
    · rw [h0, KvecM_row0 n hh a σ z, Real.norm_eq_abs]
      exact le_trans hA1 hC1le
    · rw [h1, KvecM_row1 n hh a σ z, Real.norm_eq_abs]
      exact le_trans hA2 hC2le
  · -- the value Lipschitz bound
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rcases fin2_cases i with h0 | h1
    · rw [h0, Pi.sub_apply, KvecM_row0 n hh a σ z, KvecM_row0 n hh a σ z', Real.norm_eq_abs]
      exact le_trans hG1 hM1
    · rw [h1, Pi.sub_apply, KvecM_row1 n hh a σ z, KvecM_row1 n hh a σ z', Real.norm_eq_abs]
      exact le_trans hG2 hM2
  · -- the `a`-derivative bound
    rw [KvecM_eq_row n hh σ z, pi_norm_le_iff_of_nonneg hCn]
    intro i
    rw [hderZrow]
    rcases fin2_cases i with h0 | h1
    · rw [h0, Real.norm_eq_abs]
      exact le_trans hE1 hC1le
    · rw [h1, Real.norm_eq_abs]
      exact le_trans hE2 hC2le
  · -- the `a`-derivative Lipschitz bound
    rw [KvecM_eq_row n hh σ z, KvecM_eq_row n hh σ z']
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Pi.sub_apply, hderZrow, hderZ'row]
    rcases fin2_cases i with h0 | h1
    · rw [h0, Real.norm_eq_abs]
      exact le_trans hH1 hM1
    · rw [h1, Real.norm_eq_abs]
      exact le_trans hH2 hM2

end

end Work.OddVolterra.Window

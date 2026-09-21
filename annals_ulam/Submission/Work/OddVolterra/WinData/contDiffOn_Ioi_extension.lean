import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.Anchor.extension

namespace Work.OddVolterra.WinData

open Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-!
# Extending a smooth half-line state to `(0,∞)`

The window solution `Z` is `C^∞` on `[1/4,19/20]` and equals the ball state `baseState` for
`s ≥ 9/10`, so it is `C^∞` on the half-line `[1/4,∞)`.  This file extends it to a function which is
`C^∞` on all of `ℝ` and still agrees with `Z` on `[1/4,∞)`, preserving the two row identities
`(Z 0)' = Z 2`, `(Z 1)' = Z 3` on that half-line.

The extension is the classical one (Seeley/Borel, not in Mathlib): the right jets of each component
of `Z` at `1/4` are realised by a globally smooth function (the Borel series of
`Submission/Work/Anchor/borel_series.lean`), whose difference with `Z` is flat at `1/4` and is
therefore glued to `0` on the left by `Work.Anchor.flat_glue`.
-/

/-- The first three jets of `Work.Anchor.Dlow b₀ b₁ b₂` at `0`. -/
lemma Dlow_jet_zero (b0 b1 b2 : ℝ) :
    iteratedDeriv 0 (Work.Anchor.Dlow b0 b1 b2) 0 = b0 := by
  rw [iteratedDeriv_zero, Work.Anchor.Dlow_apply]
  simp [Work.Anchor.eta0_apply, Work.Anchor.eta1_zero, Work.Anchor.eta2_zero]

lemma Dlow_jet_one (b0 b1 b2 : ℝ) :
    iteratedDeriv 1 (Work.Anchor.Dlow b0 b1 b2) 0 = b1 := by
  rw [Work.Anchor.iteratedDeriv_Dlow_apply]
  simp only [Work.Anchor.iteratedDeriv_eta0_1, Work.Anchor.iteratedDeriv_eta1_1,
    Work.Anchor.iteratedDeriv_eta2_1, mul_zero, mul_one, add_zero, zero_add]

lemma Dlow_jet_two (b0 b1 b2 : ℝ) :
    iteratedDeriv 2 (Work.Anchor.Dlow b0 b1 b2) 0 = b2 := by
  rw [Work.Anchor.iteratedDeriv_Dlow_apply]
  simp only [Work.Anchor.iteratedDeriv_eta0_2, Work.Anchor.iteratedDeriv_eta1_2,
    Work.Anchor.iteratedDeriv_eta2_2, mul_zero, mul_one, add_zero, zero_add]

/-- A `C^∞` function on a half-line `[a,∞)` extends to a globally `C^∞` function agreeing with it
on `[a,∞)` (Seeley/Borel extension: realise the one-sided jets at `a` by a smooth function, whose
difference with `f` is flat at `a`, and glue it to `0` on the left). -/
theorem exists_contDiff_eqOn_Ici {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ici a)) :
    ∃ F : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧ ∀ s : ℝ, a ≤ s → F s = f s := by
  set b0 : ℝ := iteratedDerivWithin 0 f (Ici a) a with hb0
  set b1 : ℝ := iteratedDerivWithin 1 f (Ici a) a with hb1
  set b2 : ℝ := iteratedDerivWithin 2 f (Ici a) a with hb2
  set P : ℝ → ℝ := Work.Anchor.Dlow b0 b1 b2 with hP
  have hPc : ContDiff ℝ (⊤ : ℕ∞) P := Work.Anchor.contDiff_Dlow b0 b1 b2
  have hPj0 : iteratedDeriv 0 P 0 = b0 := by rw [hP]; exact Dlow_jet_zero b0 b1 b2
  have hPj1 : iteratedDeriv 1 P 0 = b1 := by rw [hP]; exact Dlow_jet_one b0 b1 b2
  have hPj2 : iteratedDeriv 2 P 0 = b2 := by rw [hP]; exact Dlow_jet_two b0 b1 b2
  set e : ℕ → ℝ := fun k => iteratedDerivWithin k f (Ici a) a - iteratedDeriv k P 0 with he
  have he0 : ∀ k ≤ 2, e k = 0 := by
    intro k hk
    interval_cases k
    · show iteratedDerivWithin 0 f (Ici a) a - iteratedDeriv 0 P 0 = 0
      rw [hPj0, hb0]; ring
    · show iteratedDerivWithin 1 f (Ici a) a - iteratedDeriv 1 P 0 = 0
      rw [hPj1, hb1]; ring
    · show iteratedDerivWithin 2 f (Ici a) a - iteratedDeriv 2 P 0 = 0
      rw [hPj2, hb2]; ring
  obtain ⟨S, hSc, hSj, -, -, -⟩ := Work.Anchor.borel_series e he0 1 (by norm_num)
  set D : ℝ → ℝ := P + S with hD
  have hDc : ContDiff ℝ (⊤ : ℕ∞) D := hPc.add hSc
  have hDj : ∀ k : ℕ, iteratedDeriv k D 0 = iteratedDerivWithin k f (Ici a) a := by
    intro k
    have h1 : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) P 0 :=
      hPc.contDiffAt.of_le (Work.Anchor.natCast_le_topE k)
    have h2 : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) S 0 :=
      hSc.contDiffAt.of_le (Work.Anchor.natCast_le_topE k)
    rw [hD, iteratedDeriv_add h1 h2, hSj k]
    show iteratedDeriv k P 0 + (iteratedDerivWithin k f (Ici a) a - iteratedDeriv k P 0) =
      iteratedDerivWithin k f (Ici a) a
    ring
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => D (x - a)) :=
    hDc.comp (contDiff_id.sub contDiff_const)
  have hφc : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => f x - D (x - a)) (Ici a) :=
    hf.sub hcomp.contDiffOn
  have hφj : ∀ k : ℕ, iteratedDerivWithin k (fun x : ℝ => f x - D (x - a)) (Ici a) a = 0 := by
    intro k
    have hf' : ContDiffWithinAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun x : ℝ => f x) (Ici a) a :=
      (hf.contDiffWithinAt (mem_Ici.mpr le_rfl)).of_le (Work.Anchor.natCast_le_topE k)
    have hd' : ContDiffWithinAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun x : ℝ => D (x - a)) (Ici a) a :=
      ((hcomp.contDiffAt (x := a)).contDiffWithinAt).of_le (Work.Anchor.natCast_le_topE k)
    rw [show (fun x : ℝ => f x - D (x - a)) =
        (fun x : ℝ => f x) - (fun x : ℝ => D (x - a)) from rfl,
      iteratedDerivWithin_sub (mem_Ici.mpr le_rfl) (uniqueDiffOn_Ici a) hf' hd',
      Work.Anchor.iteratedDerivWithin_sub_const a k hDc, hDj k, sub_self]
  obtain ⟨hΨc, -⟩ := Work.Anchor.flat_glue a (fun x : ℝ => f x - D (x - a)) hφc hφj
  refine ⟨fun x : ℝ => D (x - a) + (if a ≤ x then f x - D (x - a) else 0), ?_, ?_⟩
  · exact hcomp.add hΨc
  · intro s hs
    show D (s - a) + (if a ≤ s then f s - D (s - a) else 0) = f s
    rw [if_pos hs]
    ring

/-! ## Smoothness of the ball state and of `Z` on the half-line -/

/-- The ball state `baseState` is smooth. -/
lemma contDiff_baseState : ContDiff ℝ (⊤ : ℕ∞) Work.OddVolterra.baseState := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · change ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  · change ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  · change ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.contDiff_deriv_of_contDiff
      Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  · change ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.contDiff_deriv_of_contDiff
      Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX

/-- `Z` is `C^∞` on the half-line `[1/4,∞)`: on `[1/4,19/20]` this is the hypothesis, and from
`9/10` on it agrees with the smooth ball state. -/
lemma contDiffOn_Z_Ici {Z : ℝ → Work.OddVolterra.St}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Icc (1 / 4 : ℝ) (19 / 20)))
    (hZtail : ∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s) :
    ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ici (1 / 4 : ℝ)) := by
  intro x hx
  rcases lt_or_ge x (19 / 20) with hxlt | hxge
  · have hmem : x ∈ Set.Icc (1 / 4 : ℝ) (19 / 20) := ⟨hx, hxlt.le⟩
    refine (hZ x hmem).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio ((x + 19 / 20) / 2), isOpen_Iio,
      by show x < (x + 19 / 20) / 2; linarith,
      fun y hy => ⟨hy.2, by have h : y < (x + 19 / 20) / 2 := hy.1; linarith⟩⟩
  · have hx9 : 9 / 10 < x := by linarith
    have hev : ∀ᶠ y in 𝓝[Set.Ici (1 / 4 : ℝ)] x, Z y = Work.OddVolterra.baseState y := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_Ioi.mem_nhds hx9] with y hy _
      exact hZtail y hy.le
    exact (contDiff_baseState.contDiffOn.contDiffWithinAt hx).congr_of_eventuallyEq hev
      (hZtail x hx9.le)

/-- The boundary argument for the row identities: if `f` is differentiable on `(a,b)` with
derivative `g` there, and `g` is continuous from the right at `a`, then the one-sided derivative of
`f` at `a` is `g a`. -/
lemma derivWithin_Ici_eq_of_tendsto_deriv {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfcont : ContinuousOn f (Set.Icc a b)) (hfdiff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hderiv : ∀ s ∈ Set.Ioo a b, deriv f s = g s)
    (hgcont : ContinuousWithinAt g (Set.Ici a) a) :
    derivWithin f (Set.Ici a) a = g a := by
  have hIoo : Set.Ioo a b ∈ 𝓝[>] a := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, hab, fun y hy => ⟨hy.2, hy.1⟩⟩
  have hHas : HasDerivWithinAt f (g a) (Set.Ici a) a := by
    refine hasDerivWithinAt_Ici_of_tendsto_deriv hfdiff ?_ hIoo ?_
    · exact (hfcont.continuousWithinAt ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
    · have hgc : Tendsto g (𝓝[>] a) (𝓝 (g a)) :=
        hgcont.mono_left (nhdsWithin_mono a Set.Ioi_subset_Ici_self)
      have hev : g =ᶠ[𝓝[>] a] deriv f := by
        filter_upwards [hIoo] with y hy
        exact (hderiv y hy).symm
      exact Filter.Tendsto.congr' hev hgc
  exact hHas.derivWithin (uniqueDiffWithinAt_Ici a)

/-- **Main lemma.**  A state `Z` which is `C^∞` on `[1/4,19/20]`, agrees with the ball state
`baseState` from `9/10` on, and satisfies the two row identities `(Z 0)' = Z 2`, `(Z 1)' = Z 3`
on `(1/4,∞)`, extends to a state `Zfin` which is `C^∞` on `(0,∞)`, agrees with `Z` on `[1/4,∞)`
and satisfies the same two row identities there. -/
theorem contDiffOn_Ioi_extension {Z : ℝ → Work.OddVolterra.St}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Icc (1 / 4 : ℝ) (19 / 20)))
    (hZtail : ∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s)
    (hrow0 : ∀ s : ℝ, 1 / 4 < s → deriv (fun u : ℝ => Z u 0) s = Z s 2)
    (hrow1 : ∀ s : ℝ, 1 / 4 < s → deriv (fun u : ℝ => Z u 1) s = Z s 3) :
    ∃ Zfin : ℝ → Work.OddVolterra.St,
      ContDiffOn ℝ (⊤ : ℕ∞) Zfin (Set.Ioi (0 : ℝ)) ∧
      (∀ s : ℝ, 1 / 4 ≤ s → Zfin s = Z s) ∧
      (∀ s : ℝ, 1 / 4 ≤ s →
        deriv (fun u : ℝ => Zfin u 0) s = Zfin s 2 ∧
        deriv (fun u : ℝ => Zfin u 1) s = Zfin s 3) := by
  have hZhalf : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ici (1 / 4 : ℝ)) := contDiffOn_Z_Ici hZ hZtail
  have hcomp : ∀ i : Fin 4,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Z s i) (Set.Ici (1 / 4 : ℝ)) :=
    fun i => (contDiffOn_pi.mp hZhalf) i
  choose Fi hFic hFieq using
    fun i : Fin 4 => exists_contDiff_eqOn_Ici (a := (1 / 4 : ℝ)) (hcomp i)
  let Zfin : ℝ → Work.OddVolterra.St := fun s => ![Fi 0 s, Fi 1 s, Fi 2 s, Fi 3 s]
  have hZfinc : ContDiff ℝ (⊤ : ℕ∞) Zfin := by
    rw [show Zfin = fun s : ℝ => ![Fi 0 s, Fi 1 s, Fi 2 s, Fi 3 s] from rfl, contDiff_pi]
    intro i
    fin_cases i
    · exact hFic 0
    · exact hFic 1
    · exact hFic 2
    · exact hFic 3
  have hZfineq : ∀ s : ℝ, 1 / 4 ≤ s → Zfin s = Z s := by
    intro s hs
    funext i
    fin_cases i
    · exact hFieq 0 s hs
    · exact hFieq 1 s hs
    · exact hFieq 2 s hs
    · exact hFieq 3 s hs
  have hbnd : ∀ (i j : Fin 4),
      (∀ s : ℝ, 1 / 4 < s → deriv (fun u : ℝ => Z u i) s = Z s j) →
      derivWithin (fun u : ℝ => Z u i) (Set.Ici (1 / 4 : ℝ)) (1 / 4) = Z (1 / 4) j := by
    intro i j hrow
    refine derivWithin_Ici_eq_of_tendsto_deriv (f := fun u : ℝ => Z u i)
      (g := fun u : ℝ => Z u j) (by norm_num : (1 / 4 : ℝ) < 19 / 20) ?_ ?_ ?_ ?_
    · exact ((contDiffOn_pi.mp hZ) i).continuousOn
    · exact ((contDiffOn_pi.mp hZ) i).differentiableOn (by simp) |>.mono Ioo_subset_Icc_self
    · intro s hs
      exact hrow s hs.1
    · exact ((contDiffOn_pi.mp hZhalf) j).continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)
  have hb0 : derivWithin (fun u : ℝ => Z u 0) (Set.Ici (1 / 4 : ℝ)) (1 / 4) = Z (1 / 4) 2 :=
    hbnd 0 2 hrow0
  have hb1 : derivWithin (fun u : ℝ => Z u 1) (Set.Ici (1 / 4 : ℝ)) (1 / 4) = Z (1 / 4) 3 :=
    hbnd 1 3 hrow1
  refine ⟨Zfin, hZfinc.contDiffOn, hZfineq, ?_⟩
  intro s hs
  constructor
  · rcases eq_or_lt_of_le hs with h | h
    · subst h
      have hder : deriv (fun u : ℝ => Zfin u 0) (1 / 4)
          = derivWithin (fun u : ℝ => Z u 0) (Set.Ici (1 / 4 : ℝ)) (1 / 4) :=
        Work.Anchor.deriv_eq_derivWithin_of_contDiff_eqOn (1 / 4) (hFic 0)
          (fun x hx => hFieq 0 x hx) (1 / 4) le_rfl
      rw [hder, hb0]
      exact (hFieq 2 (1 / 4) le_rfl).symm
    · have hev : (fun u : ℝ => Zfin u 0) =ᶠ[𝓝 s] (fun u : ℝ => Z u 0) := by
        filter_upwards [isOpen_Ioi.mem_nhds h] with u hu
        exact congrFun (hZfineq u hu.le) 0
      rw [Filter.EventuallyEq.deriv_eq hev, hrow0 s h]
      exact (congrFun (hZfineq s hs) 2).symm
  · rcases eq_or_lt_of_le hs with h | h
    · subst h
      have hder : deriv (fun u : ℝ => Zfin u 1) (1 / 4)
          = derivWithin (fun u : ℝ => Z u 1) (Set.Ici (1 / 4 : ℝ)) (1 / 4) :=
        Work.Anchor.deriv_eq_derivWithin_of_contDiff_eqOn (1 / 4) (hFic 1)
          (fun x hx => hFieq 1 x hx) (1 / 4) le_rfl
      rw [hder, hb1]
      exact (hFieq 3 (1 / 4) le_rfl).symm
    · have hev : (fun u : ℝ => Zfin u 1) =ᶠ[𝓝 s] (fun u : ℝ => Z u 1) := by
        filter_upwards [isOpen_Ioi.mem_nhds h] with u hu
        exact congrFun (hZfineq u hu.le) 1
      rw [Filter.EventuallyEq.deriv_eq hev, hrow1 s h]
      exact (congrFun (hZfineq s hs) 3).symm


end

end Work.OddVolterra.WinData

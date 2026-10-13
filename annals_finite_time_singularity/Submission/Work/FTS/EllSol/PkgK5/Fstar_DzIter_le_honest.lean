/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular moments of the radially differentiated solution vanish, at the honest level

The target is

`F_*(D_z^i Ψ)(z) = 0`  for all `i ≤ k+3` and all `z > 0`,

for a datum `(F, Ψ)` of the weak class `TT.EllWeakPos α k` with `k ≥ 2`, together with the
*extra honesty* `HkMem α (k+3) (z²∂_z²Ψ)` of the second radial derivative.

## Shape of the argument

Write `M_i(z) := F_*(D_z^i Ψ)(z)` and `A := z²∂_z²Ψ`.  The starting point is the *radial*
moment tower for `A`: for every `j` with `j+1 ≤ k+3`,

  `B_j(z) - B_j(s) = ∫_s^z B_{j+1}(r)/r dr`,   `B_j := Bmom A j`,

(`Cert.radIter_bmom_chain`, which needs only `SmoothOpen A` and `HkMem α (k+3) A`), and the
identity `B_j = F_*(D_z^j A)` (`Bmom_eq_Fstar_DzIter`).  The bridge to `M` is the structural
identity

  `D_z^j A = D_z^{j+2} Ψ - D_z^{j+1} Ψ`    on the open quadrant

(`H2W.DzIter_zsq_pzIter2_eq`), i.e. `B_j = M_{j+2} - M_{j+1}` whenever the two slices are
integrable.

The argument is then

* the levels `i ≤ k+1` are handled by the *level-2* theorem `H2W.Fstar_DzIter_le_Psi` applied
  to the radially shifted data `(D_z^j F, D_z^j Ψ)` (`Cores.Repair.EllWeakPos_DzIter_one_shift`,
  iterated), which needs only `HkMem α 2` of the shifted `z²∂_z²Ψ` and `∂_θ²Ψ`;
* with `M_k = M_{k+1} = 0` the identity above gives `B_{k-1} = 0`, and the tower for `B` at
  level `k-1` then gives `∫_s^z B_k(r)/r dr = 0` for all `0 < s ≤ z`; since `B_k` is continuous
  on `(0,∞)` (`Cert.radIter_bmom_continuousOn`) this forces `B_k = 0`, hence
  `M_{k+2} = M_{k+1} + B_k = 0`; the same step at level `k` gives `B_{k+1} = 0` and hence
  `M_{k+3} = M_{k+2} + B_{k+1} = 0`.

The only place where the extra hypothesis `HkMem α (k+3) (z²∂_z²Ψ)` is used (besides the tower
itself) is the integrability of the two *top* slices `D_z^{k+2}Ψ·σ`, `D_z^{k+3}Ψ·σ`, which is
obtained by splitting them through the identity as `D_z^{k+1}Ψ + D_z^k A` resp.
`D_z^{k+2}Ψ + D_z^{k+1} A` and using the honesty of `A` (`abs_moment_le_energy`).

The module is complete: every declaration below is proved, and the final theorem depends only
on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Cores.Repair.DzShift
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.Cert.radIter_Bmom_ae
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option maxHeartbeats 1600000

local notation "Fstar" => Work.Elliptic.Fstar
local notation "sg" => Work.Elliptic.sinCos2
local notation "DzIt" => Work.Spaces.DzIter

/-! ## 1. Descending the weak class, and the radially shifted data -/

/-- **The weak class is monotone in the level.**  Only the four `HkMem` clauses carry the
level; the equation, the Dirichlet data, the moments and the smoothness do not. -/
theorem EllWeakPos_descend {α : ℝ} {K l : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hlK : l ≤ K)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α K F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α l F Ψ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cores.Repair.SmoothOpen_of_bslOp_eq hΨ
      (fun z θ hz hθ hlt => h.eq z hz θ hθ hlt)
  have hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨ
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hΨ.pth).pth
  have hSZ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) := hSB.Dz
  exact ⟨h.eq, h.zero, h.pi_half, h.orthF, h.orthPsi, h.smooth,
    Work.FTS.OpenPkg.HkMem_mono_open hSF l hlK h.memF,
    Work.FTS.OpenPkg.HkMem_mono_open hSA l hlK h.memA,
    Work.FTS.OpenPkg.HkMem_mono_open hSB l hlK h.memB,
    Work.FTS.OpenPkg.HkMem_mono_open hSZ l hlK h.memZPth2⟩

/-- **The iterated radial shift of the weak class**: from `EllWeakPos α k` at level `k` we get
`EllWeakPos α (k-j)` for the data `(D_z^j F, D_z^j Ψ)`, as long as `k-j ≥ 2`. -/
theorem EllWeakPos_DzIter_shift_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ j : ℕ, j ≤ k - 2 →
      Work.FTS.EllipticEst.TT.EllWeakPos α (k - j) (DzIt j F) (DzIt j Ψ) := by
  intro j
  induction j with
  | zero => intro _; simpa using h
  | succ j ih =>
      intro hj
      have hj' : j ≤ k - 2 := by omega
      have hk' : 2 ≤ k - j := by omega
      have hstep :=
        Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le hk' (ih hj')
      have h1F := Work.Spaces.DzIter_add_right 1 j F
      have h1Ψ := Work.Spaces.DzIter_add_right 1 j Ψ
      have h1j : 1 + j = j + 1 := by omega
      rw [h1j] at h1F h1Ψ
      have eF : DzIt 1 (DzIt j F) = DzIt (j + 1) F := h1F.symm
      have eΨ : DzIt 1 (DzIt j Ψ) = DzIt (j + 1) Ψ := h1Ψ.symm
      have ek : k - j - 1 = k - (j + 1) := by omega
      rw [eF, eΨ, ek] at hstep
      exact hstep

/-! ## 2. The moments of the levels `≤ k+1` -/

/-- **All the moments up to level `k+1` vanish.**  Apply the level-`2` theorem
`H2W.Fstar_DzIter_le_Psi` to the shifted data `(D_z^j F, D_z^j Ψ)` with `j := max 0 (m-3)`:
the shifted datum is at level `k - j ≥ 2` and the index `m - j` is at most `3`. -/
theorem lowMom_zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ m : ℕ, m ≤ k + 1 → ∀ z : ℝ, 0 < z → Fstar (DzIt m Ψ) z = 0 := by
  intro m hm z hz
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, (j = 0 ∧ m ≤ 3) ∨ (j = m - 3 ∧ 4 ≤ m) := by
    by_cases h3 : m ≤ 3
    · exact ⟨0, Or.inl ⟨rfl, h3⟩⟩
    · exact ⟨m - 3, Or.inr ⟨rfl, by omega⟩⟩
  have hj : j ≤ k - 2 := by
    rcases hjdef with ⟨rfl, hm3⟩ | ⟨rfl, hm4⟩ <;> omega
  have hshift := EllWeakPos_DzIter_shift_le hk h j hj
  have h2 : Work.FTS.EllipticEst.TT.EllWeakPos α 2 (DzIt j F) (DzIt j Ψ) :=
    EllWeakPos_descend (l := 2) (by omega) hshift
  have hmi : m - j ≤ 3 := by
    rcases hjdef with ⟨rfl, hm3⟩ | ⟨rfl, hm4⟩ <;> omega
  have hmj : m - j + j = m := by
    rcases hjdef with ⟨rfl, hm3⟩ | ⟨rfl, hm4⟩ <;> omega
  have hres := Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi α (DzIt j F) (DzIt j Ψ) h2
    (m - j) hmi z hz
  have hfun : DzIt (m - j) (DzIt j Ψ) = DzIt m Ψ := by
    have h1 := Work.Spaces.DzIter_add_right (m - j) j Ψ
    rw [hmj] at h1
    exact h1.symm
  rwa [hfun] at hres

/-! ## 3. Slice integrability

`A := z²∂_z²Ψ` is honest at level `k+3`, so every `D_z^q A` has an integrable `σ`-slice
(`abs_moment_le_energy`).  The levels `k` and `k+1` *of `Ψ`* come from the level-`2` slice
bounds (`H2W.level_bound`) applied to the shifted datum; the two top levels `k+2`, `k+3` are
obtained by splitting through the structural identity. -/

/-- The `σ`-slice of `D_z^q A` is integrable, for `q ≤ k+3`. -/
theorem Aslice_integrable {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    {q : ℕ} (hq : q ≤ k + 3) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ => DzIt q (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ
      * sg θ) Work.Spaces.Iθ :=
  (Work.FTS.EllipticEst.H2W.abs_moment_le_energy
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (hSA.DzIter q).continuousOn hu)
    (Work.FTS.EllipticEst.H2W.slot_slice_integrableOn hSA hA q hq hu)).1

/-- The `σ`-slice of `D_z^k Ψ` is integrable. -/
theorem Psislice_k {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ u : ℝ, 0 < u → IntegrableOn (fun θ => DzIt k Ψ u θ * sg θ) Work.Spaces.Iθ := by
  have hshift := EllWeakPos_DzIter_shift_le hk h (k - 2) (by omega)
  have h2 : Work.FTS.EllipticEst.TT.EllWeakPos α 2 (DzIt (k - 2) F) (DzIt (k - 2) Ψ) :=
    EllWeakPos_descend (l := 2) (by omega) hshift
  have hΨ' : Work.FTS.EllipticEst.SmoothOpen (DzIt (k - 2) Ψ) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth).DzIter (k - 2)
  have hfun : DzIt 2 (DzIt (k - 2) Ψ) = DzIt k Ψ := by
    have h1 := Work.Spaces.DzIter_add_right 2 (k - 2) Ψ
    rw [show 2 + (k - 2) = k from by omega] at h1
    exact h1.symm
  intro u hu
  have hb := (Work.FTS.EllipticEst.H2W.level_bound hΨ' h2.memA h2.memB 2 (by norm_num)).1 u hu
  rwa [hfun] at hb

/-- The `σ`-slice of `D_z^{k+1} Ψ` is integrable. -/
theorem Psislice_k1 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ u : ℝ, 0 < u → IntegrableOn (fun θ => DzIt (k + 1) Ψ u θ * sg θ) Work.Spaces.Iθ := by
  have hshift := EllWeakPos_DzIter_shift_le hk h (k - 2) (by omega)
  have h2 : Work.FTS.EllipticEst.TT.EllWeakPos α 2 (DzIt (k - 2) F) (DzIt (k - 2) Ψ) :=
    EllWeakPos_descend (l := 2) (by omega) hshift
  have hΨ' : Work.FTS.EllipticEst.SmoothOpen (DzIt (k - 2) Ψ) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth).DzIter (k - 2)
  have hfun : DzIt 3 (DzIt (k - 2) Ψ) = DzIt (k + 1) Ψ := by
    have h1 := Work.Spaces.DzIter_add_right 3 (k - 2) Ψ
    rw [show 3 + (k - 2) = k + 1 from by omega] at h1
    exact h1.symm
  intro u hu
  have hb := (Work.FTS.EllipticEst.H2W.level_bound hΨ' h2.memA h2.memB 3 (by norm_num)).1 u hu
  rwa [hfun] at hb

/-- The `σ`-slice of `D_z^{k+2} Ψ` is integrable: split `D_z^{k+2}Ψ = D_z^{k+1}Ψ + D_z^k A`. -/
theorem Psislice_k2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ u : ℝ, 0 < u → IntegrableOn (fun θ => DzIt (k + 2) Ψ u θ * sg θ) Work.Spaces.Iθ := by
  intro u hu
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpt : (fun θ => DzIt (k + 2) Ψ u θ * sg θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (DzIt (k + 1) Ψ u θ
        + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.H2W.ae_Ioo_mem,
      self_mem_ae_restrict measurableSet_Icc] with θ hθ _
    have hid := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨ k hu hθ
    rw [hid]
    ring
  have hsum : IntegrableOn (fun θ => (DzIt (k + 1) Ψ u θ
      + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) * sg θ)
      Work.Spaces.Iθ := by
    refine ((Psislice_k1 hk h u hu).add
      (Aslice_integrable (q := k) hSA hA (by omega) hu)).congr ?_
    filter_upwards with θ
    simp only [Pi.add_apply]
    ring
  exact hsum.congr hpt.symm

/-- The `σ`-slice of `D_z^{k+3} Ψ` is integrable: split `D_z^{k+3}Ψ = D_z^{k+2}Ψ + D_z^{k+1}A`. -/
theorem Psislice_k3 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ u : ℝ, 0 < u → IntegrableOn (fun θ => DzIt (k + 3) Ψ u θ * sg θ) Work.Spaces.Iθ := by
  intro u hu
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpt : (fun θ => DzIt (k + 3) Ψ u θ * sg θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (DzIt (k + 2) Ψ u θ
        + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.H2W.ae_Ioo_mem,
      self_mem_ae_restrict measurableSet_Icc] with θ hθ _
    have hid := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨ (k + 1) hu hθ
    rw [show k + 1 + 2 = k + 3 from by omega,
      show k + 1 + 1 = k + 2 from by omega] at hid
    rw [hid]
    ring
  have hsum : IntegrableOn (fun θ => (DzIt (k + 2) Ψ u θ
      + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) * sg θ)
      Work.Spaces.Iθ := by
    refine ((Psislice_k2 hk h hSA hA u hu).add
      (Aslice_integrable (q := k + 1) hSA hA (by omega) hu)).congr ?_
    filter_upwards with θ
    simp only [Pi.add_apply]
    ring
  exact hsum.congr hpt.symm

/-! ## 4. The top two moments -/

/-- **`B_{k-1} = F_*(D_z^{k-1} A) = 0`.**  On the open quadrant `D_z^{k-1}A = D_z^{k+1}Ψ - D_z^k Ψ`,
and both slices are integrable, so the integral splits and `M_{k+1} = M_k = 0`. -/
theorem Bmom_low_zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z : ℝ, 0 < z → Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k - 1) z = 0 := by
  intro z hz
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpt : (fun θ => DzIt (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (DzIt (k + 1) Ψ z θ - DzIt k Ψ z θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.H2W.ae_Ioo_mem,
      self_mem_ae_restrict measurableSet_Icc] with θ hθ _
    have hid := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨ (k - 1) hz hθ
    rw [show k - 1 + 2 = k + 1 from by omega,
      show k - 1 + 1 = k from by omega] at hid
    rw [hid]
  rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter, Work.Elliptic.Fstar,
    MeasureTheory.integral_congr_ae hpt]
  have hsplit : (fun θ => (DzIt (k + 1) Ψ z θ - DzIt k Ψ z θ) * sg θ)
      = fun θ => DzIt (k + 1) Ψ z θ * sg θ - DzIt k Ψ z θ * sg θ := by
    funext θ
    ring
  rw [hsplit, MeasureTheory.integral_sub (Psislice_k1 hk h z hz) (Psislice_k hk h z hz)]
  have h1 : (∫ a in Work.Spaces.Iθ, DzIt (k + 1) Ψ z a * sg a) = 0 :=
    lowMom_zero hk h (k + 1) (by omega) z hz
  have h2 : (∫ a in Work.Spaces.Iθ, DzIt k Ψ z a * sg a) = 0 :=
    lowMom_zero hk h k (by omega) z hz
  rw [h1, h2, sub_self]

/-- **`B_k = 0`.**  With `B_{k-1} = 0`, the moment tower at level `k-1` gives
`∫_s^z B_k(r)/r dr = 0` for all `0 < s ≤ z`, and `B_k/r` is continuous on `(0,∞)`. -/
theorem Bmom_k_zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k z = 0 := by
  have hlow : ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k - 1) z = 0 :=
    Bmom_low_zero (F := F) hk h
  have hcont : ContinuousOn (fun r : ℝ => Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k r / r) (Set.Ioi 0) :=
    (Work.FTS.EllipticEst.Cert.radIter_bmom_continuousOn
      (F := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) α (k + 3) hSA hA k (by omega)).div
      continuousOn_id (fun r hr => (show (0 : ℝ) < r from hr).ne')
  intro z hz
  have hV : Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k z / z = 0 := by
    refine Work.FTS.EllipticEst.H2W.eq_zero_of_interval_integral_eq_zero
      (V := fun r : ℝ => Work.FTS.EllipticEst.Bmom
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k r / r) hz (fun s w hs hsw => ?_) hcont
    have hchain := Work.FTS.EllipticEst.Cert.radIter_bmom_chain
      (F := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) α (k + 3) hSA hA (k - 1) (by omega) hs hsw
    rw [show k - 1 + 1 = k from by omega] at hchain
    rw [← hchain, hlow w (lt_of_lt_of_le hs hsw), hlow s hs, sub_self]
  rcases (div_eq_zero_iff.mp hV) with h' | h'
  · exact h'
  · exact absurd h' (ne_of_gt hz)

/-- **`B_{k+1} = 0`**, by the same argument with `B_k = 0`. -/
theorem Bmom_k1_zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k + 1) z = 0 := by
  have hprev : ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k z = 0 :=
    Bmom_k_zero (F := F) hk h hSA hA
  have hcont : ContinuousOn (fun r : ℝ => Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k + 1) r / r) (Set.Ioi 0) :=
    (Work.FTS.EllipticEst.Cert.radIter_bmom_continuousOn
      (F := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) α (k + 3) hSA hA (k + 1) (by omega)).div
      continuousOn_id (fun r hr => (show (0 : ℝ) < r from hr).ne')
  intro z hz
  have hV : Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k + 1) z / z = 0 := by
    refine Work.FTS.EllipticEst.H2W.eq_zero_of_interval_integral_eq_zero
      (V := fun r : ℝ => Work.FTS.EllipticEst.Bmom
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k + 1) r / r) hz
      (fun s w hs hsw => ?_) hcont
    have hchain := Work.FTS.EllipticEst.Cert.radIter_bmom_chain
      (F := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) α (k + 3) hSA hA k (by omega) hs hsw
    rw [← hchain, hprev w (lt_of_lt_of_le hs hsw), hprev s hs, sub_self]
  rcases (div_eq_zero_iff.mp hV) with h' | h'
  · exact h'
  · exact absurd h' (ne_of_gt hz)

/-- **`M_{k+2} = 0`**: `D_z^{k+2}Ψ = D_z^{k+1}Ψ + D_z^k A` a.e., and the two integrals vanish. -/
theorem Mom_k2_zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ z : ℝ, 0 < z → Fstar (DzIt (k + 2) Ψ) z = 0 := by
  intro z hz
  have hpt : (fun θ => DzIt (k + 2) Ψ z θ * sg θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (DzIt (k + 1) Ψ z θ
        + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.H2W.ae_Ioo_mem,
      self_mem_ae_restrict measurableSet_Icc] with θ hθ _
    have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
    have hid := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨ k hz hθ
    rw [hid]
    ring
  rw [Work.Elliptic.Fstar, MeasureTheory.integral_congr_ae hpt]
  have hsplit : (fun θ => (DzIt (k + 1) Ψ z θ
        + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
      = fun θ => DzIt (k + 1) Ψ z θ * sg θ
        + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ := by
    funext θ
    ring
  rw [hsplit, MeasureTheory.integral_add (Psislice_k1 hk h z hz)
    (Aslice_integrable (q := k) hSA hA (by omega) hz)]
  have h1 : (∫ a in Work.Spaces.Iθ, DzIt (k + 1) Ψ z a * sg a) = 0 :=
    lowMom_zero hk h (k + 1) (by omega) z hz
  have h2 : (∫ a in Work.Spaces.Iθ, DzIt k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z a * sg a) = 0 :=
    Bmom_k_zero (F := F) hk h hSA hA z hz
  rw [h1, h2, add_zero]

/-- **`M_{k+3} = 0`**: `D_z^{k+3}Ψ = D_z^{k+2}Ψ + D_z^{k+1} A` a.e. -/
theorem Mom_k3_zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ z : ℝ, 0 < z → Fstar (DzIt (k + 3) Ψ) z = 0 := by
  intro z hz
  have hpt : (fun θ => DzIt (k + 3) Ψ z θ * sg θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (DzIt (k + 2) Ψ z θ
        + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.H2W.ae_Ioo_mem,
      self_mem_ae_restrict measurableSet_Icc] with θ hθ _
    have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
    have hid := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨ (k + 1) hz hθ
    rw [show k + 1 + 2 = k + 3 from by omega,
      show k + 1 + 1 = k + 2 from by omega] at hid
    rw [hid]
    ring
  rw [Work.Elliptic.Fstar, MeasureTheory.integral_congr_ae hpt]
  have hsplit : (fun θ => (DzIt (k + 2) Ψ z θ
        + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
      = fun θ => DzIt (k + 2) Ψ z θ * sg θ
        + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ := by
    funext θ
    ring
  rw [hsplit, MeasureTheory.integral_add (Psislice_k2 hk h hSA hA z hz)
    (Aslice_integrable (q := k + 1) hSA hA (by omega) hz)]
  have h1 : (∫ a in Work.Spaces.Iθ, DzIt (k + 2) Ψ z a * sg a) = 0 :=
    Mom_k2_zero hk h hSA hA z hz
  have h2 : (∫ a in Work.Spaces.Iθ, DzIt (k + 1)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z a * sg a) = 0 :=
    Bmom_k1_zero (F := F) hk h hSA hA z hz
  rw [h1, h2, add_zero]

/-! ## 5. The target -/

theorem Fstar_DzIter_le_honest {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hA : Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ i : ℕ, i ≤ k + 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i Ψ) z = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨ
  intro i hi z hz
  by_cases hlow : i ≤ k + 1
  · exact lowMom_zero hk h i hlow z hz
  · have hcases : i = k + 2 ∨ i = k + 3 := by omega
    rcases hcases with rfl | rfl
    · exact Mom_k2_zero hk h hSA hA z hz
    · exact Mom_k3_zero hk h hSA hA z hz

end Work.FTS.EllSol.PkgK5

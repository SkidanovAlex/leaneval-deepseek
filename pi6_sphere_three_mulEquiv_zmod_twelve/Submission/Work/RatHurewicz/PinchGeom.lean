import Mathlib
import Submission.Work.RatHurewicz.FillFamilyDefs

/-!
# The pinch geometry of the cube boundary

... (see FillFamilyDefs for the description)
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

/-- The `ℓ∞` radial coordinate of a point of `I^m`: `0` at the centre, `1` on `∂I^m`. -/
def finNonempty {m : ℕ} (hm : 1 ≤ m) : (Finset.univ : Finset (Fin m)).Nonempty :=
  ⟨⟨0, hm⟩, Finset.mem_univ _⟩

def sig (m : ℕ) (hm : 1 ≤ m) (u : IC m) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' (finNonempty hm) (fun i => |2 * (u i : ℝ) - 1|)

theorem sig_def (m : ℕ) (hm : 1 ≤ m) (u : IC m) :
    sig m hm u = (Finset.univ : Finset (Fin m)).sup' (finNonempty hm)
      (fun i => |2 * (u i : ℝ) - 1|) := rfl

theorem continuous_sig (m : ℕ) (hm : 1 ≤ m) : Continuous (sig m hm) :=
  Continuous.finset_sup'_apply (s := Finset.univ) (finNonempty hm) fun i _ =>
    ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub
      continuous_const).abs

theorem sig_nonneg (m : ℕ) (hm : 1 ≤ m) (u : IC m) : 0 ≤ sig m hm u := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finNonempty hm)
    (fun i => |2 * (u i : ℝ) - 1|)
  rw [show sig m hm u = |2 * (u i : ℝ) - 1| from hi]; positivity

theorem sig_le_one (m : ℕ) (hm : 1 ≤ m) (u : IC m) : sig m hm u ≤ 1 := by
  rw [sig]
  refine Finset.sup'_le _ (fun i => |2 * (u i : ℝ) - 1|) fun i _ => ?_
  have h0 : (0:ℝ) ≤ (u i : ℝ) := (u i).2.1
  have h1 : (u i : ℝ) ≤ 1 := (u i).2.2
  rw [abs_le]; constructor <;> linarith

theorem sig_le (m : ℕ) (hm : 1 ≤ m) (u : IC m) (i : Fin m) :
    |2 * (u i : ℝ) - 1| ≤ sig m hm u := by
  rw [sig]
  exact (Finset.le_sup'_iff (finNonempty hm)).mpr ⟨i, Finset.mem_univ i, le_rfl⟩

theorem sig_eq_one_iff (m : ℕ) (hm : 1 ≤ m) (u : IC m) :
    sig m hm u = 1 ↔ u ∈ Cube.boundary (Fin m) := by
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finNonempty hm)
      (fun i => |2 * (u i : ℝ) - 1|)
    have hs : sig m hm u = |2 * (u i : ℝ) - 1| := by rw [sig_def]; exact hi
    have hi1 : |2 * (u i : ℝ) - 1| = 1 := by rw [← hs]; exact h
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hi1 with h2 | h2
    · refine ⟨i, Or.inr ?_⟩
      apply Subtype.ext
      show ((u i : unitInterval) : ℝ) = 1
      linarith
    · refine ⟨i, Or.inl ?_⟩
      apply Subtype.ext
      show ((u i : unitInterval) : ℝ) = 0
      linarith
  · rintro ⟨i, hi | hi⟩
    · have h3 : ((u i : unitInterval) : ℝ) = 0 := congrArg Subtype.val hi
      have h2 : |2 * (u i : ℝ) - 1| = 1 := by rw [h3]; norm_num
      exact le_antisymm (sig_le_one m hm u) (by rw [← h2]; exact sig_le m hm u i)
    · have h3 : ((u i : unitInterval) : ℝ) = 1 := congrArg Subtype.val hi
      have h2 : |2 * (u i : ℝ) - 1| = 1 := by rw [h3]; norm_num
      exact le_antisymm (sig_le_one m hm u) (by rw [← h2]; exact sig_le m hm u i)

/-- If `u` is the centre of `I^m` then `sig u = 0`. -/
theorem sig_eq_zero_of_center (m : ℕ) (hm : 1 ≤ m) (u : IC m)
    (hu : ∀ i, (u i : ℝ) = 1/2) : sig m hm u = 0 := by
  refine le_antisymm ?_ (sig_nonneg m hm u)
  rw [sig]
  refine Finset.sup'_le _ _ fun i _ => ?_
  rw [hu i]; norm_num

/-- The `ℓ∞` "time" coordinate of `iota`: `1` when `sig ≤ 1/2`, `2 - 2 sig` for `sig ≥ 1/2`. -/
def tauR (m : ℕ) (hm : 1 ≤ m) (u : IC m) : ℝ := min 1 (2 - 2 * sig m hm u)

theorem continuous_tauR (m : ℕ) (hm : 1 ≤ m) : Continuous (tauR m hm) :=
  continuous_const.min (continuous_const.sub (continuous_const.mul (continuous_sig m hm)))

theorem tauR_nonneg (m : ℕ) (hm : 1 ≤ m) (u : IC m) : 0 ≤ tauR m hm u :=
  le_min (by norm_num) (by linarith [sig_le_one m hm u])

theorem tauR_le_one (m : ℕ) (hm : 1 ≤ m) (u : IC m) : tauR m hm u ≤ 1 :=
  min_le_left _ _

/-- The time coordinate of `iota`, as an element of `I`. -/
def tau (m : ℕ) (hm : 1 ≤ m) (u : IC m) : unitInterval :=
  ⟨tauR m hm u, tauR_nonneg m hm u, tauR_le_one m hm u⟩

@[simp] theorem tau_coe (m : ℕ) (hm : 1 ≤ m) (u : IC m) :
    ((tau m hm u : unitInterval) : ℝ) = tauR m hm u := rfl

theorem continuous_tau (m : ℕ) (hm : 1 ≤ m) : Continuous (tau m hm) :=
  Continuous.subtype_mk (continuous_tauR m hm) _

/-- The `i`-th coordinate of the radial point of `u`. -/
def radialR (m : ℕ) (hm : 1 ≤ m) (u : IC m) (i : Fin m) : ℝ :=
  1/2 + ((u i : ℝ) - 1/2) / max (sig m hm u) (1/2)

theorem radialR_eq_affine (m : ℕ) (hm : 1 ≤ m) (u : IC m) (i : Fin m) :
    radialR m hm u i
      = (1 - 1 / max (sig m hm u) (1/2)) * (1/2) + (1 / max (sig m hm u) (1/2)) * (u i : ℝ) := by
  rw [radialR]; field_simp; ring

theorem radialR_mem (m : ℕ) (hm : 1 ≤ m) (u : IC m) (i : Fin m) :
    radialR m hm u i ∈ Set.Icc (0:ℝ) 1 := by
  have hs := sig_le m hm u i
  have hsnn := sig_nonneg m hm u
  have hden : (0:ℝ) < max (sig m hm u) (1/2) := lt_max_of_lt_right (by norm_num)
  have hle : |(u i : ℝ) - 1/2| ≤ max (sig m hm u) (1/2) / 2 := by
    have h2 : (2 * (u i : ℝ) - 1) / 2 = (u i : ℝ) - 1/2 := by ring
    rw [← h2, abs_div]
    have h3 : |(2:ℝ)| = 2 := by norm_num
    rw [h3, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith [le_max_left (sig m hm u) ((1:ℝ)/2)]
  have hb := abs_le.mp hle
  rw [radialR]
  constructor
  · have : -((1:ℝ)/2) ≤ ((u i : ℝ) - 1/2) / max (sig m hm u) (1/2) := by
      rw [le_div_iff₀ hden]; linarith [hb.1]
    linarith
  · have : ((u i : ℝ) - 1/2) / max (sig m hm u) (1/2) ≤ (1:ℝ)/2 := by
      rw [div_le_iff₀ hden]; linarith [hb.2]
    linarith

/-- The radial point of `u`: the point on the ray from the centre through `u` at normalised
radius (equal to `u` itself when `sig u ≥ 1/2`). -/
def radialPt (m : ℕ) (hm : 1 ≤ m) (u : IC m) : IC m :=
  fun i => ⟨radialR m hm u i, (radialR_mem m hm u i).1, (radialR_mem m hm u i).2⟩

@[simp] theorem radialPt_coe (m : ℕ) (hm : 1 ≤ m) (u : IC m) (i : Fin m) :
    ((radialPt m hm u i : unitInterval) : ℝ) = radialR m hm u i := rfl

theorem continuous_radialR (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    Continuous fun u : IC m => radialR m hm u i := by
  have h1 : Continuous fun u : IC m => ((u i : unitInterval) : ℝ) :=
    continuous_subtype_val.comp (continuous_apply i)
  have h2 : Continuous fun u : IC m => max (sig m hm u) ((1:ℝ)/2) :=
    (continuous_sig m hm).max continuous_const
  exact continuous_const.add
    (Continuous.div (h1.sub continuous_const) h2
      (fun u => ne_of_gt (lt_max_of_lt_right (by norm_num))))

theorem continuous_radialPt_coord (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    Continuous fun u : IC m => radialPt m hm u i :=
  Continuous.subtype_mk (continuous_radialR m hm i) _

theorem continuous_radialPt (m : ℕ) (hm : 1 ≤ m) : Continuous (radialPt m hm) :=
  continuous_pi fun i => continuous_radialPt_coord m hm i

/-- The pinch inclusion `I^m → I^{m+1}`, `u ↦ (radialPt u, tau u)`. -/
def iotaFun (m : ℕ) (hm : 1 ≤ m) (u : IC m) : IC (m + 1) :=
  Fin.snoc (radialPt m hm u) (tau m hm u)

@[simp] theorem iotaFun_last (m : ℕ) (hm : 1 ≤ m) (u : IC m) :
    iotaFun m hm u (Fin.last m) = tau m hm u := by simp [iotaFun]

@[simp] theorem iotaFun_castSucc (m : ℕ) (hm : 1 ≤ m) (u : IC m) (i : Fin m) :
    iotaFun m hm u (Fin.castSucc i) = radialPt m hm u i := by simp [iotaFun]

theorem continuous_iotaFun (m : ℕ) (hm : 1 ≤ m) : Continuous (iotaFun m hm) := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [ContinuousAt, tendsto_pi_nhds]
  intro j
  cases j using Fin.lastCases with
  | last => simp only [iotaFun_last]; exact (continuous_tau m hm).continuousAt
  | cast i => simp only [iotaFun_castSucc]; exact (continuous_radialPt_coord m hm i).continuousAt

/-- `iota u` lies on the boundary of `I^{m+1}`. -/
theorem iotaFun_mem_boundary (m : ℕ) (hm : 1 ≤ m) (u : IC m) :
    iotaFun m hm u ∈ Cube.boundary (Fin (m + 1)) := by
  by_cases hsig : sig m hm u = 1
  · refine ⟨Fin.last m, Or.inl ?_⟩
    rw [iotaFun_last]
    apply Subtype.ext
    rw [tau_coe, tauR, hsig]
    norm_num
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finNonempty hm)
      (fun i => |2 * (u i : ℝ) - 1|)
    have hs : sig m hm u = |2 * (u i : ℝ) - 1| := by rw [sig_def]; exact hi
    have hlt : sig m hm u < 1 := lt_of_le_of_ne (sig_le_one m hm u) hsig
    by_cases hhalf : (1/2 : ℝ) ≤ sig m hm u
    · have hmax : max (sig m hm u) ((1:ℝ)/2) = sig m hm u := max_eq_left hhalf
      have hi1 : |2 * (u i : ℝ) - 1| = sig m hm u := hs.symm
      have hne : sig m hm u ≠ 0 := by linarith
      refine ⟨Fin.castSucc i, ?_⟩
      rw [iotaFun_castSucc]
      have hri : ((radialPt m hm u i : unitInterval) : ℝ)
          = 1/2 + ((u i : ℝ) - 1/2) / sig m hm u := by
        rw [radialPt_coe, radialR, hmax]
      rcases (abs_eq (sig_nonneg m hm u)).mp hi1 with h' | h'
      · refine Or.inr ?_
        apply Subtype.ext
        rw [hri]
        have hx : (u i : ℝ) - 1/2 = sig m hm u / 2 := by linarith
        rw [hx]
        have h1 : (sig m hm u / 2) / sig m hm u = 1/2 := by
          rw [div_eq_iff hne]; ring
        rw [h1]; norm_num
      · refine Or.inl ?_
        apply Subtype.ext
        rw [hri]
        have hx : (u i : ℝ) - 1/2 = -(sig m hm u) / 2 := by linarith
        rw [hx]
        have h1 : (-(sig m hm u) / 2) / sig m hm u = -1/2 := by
          rw [div_eq_iff hne]; ring
        rw [h1]; norm_num
    · push_neg at hhalf
      refine ⟨Fin.last m, Or.inr ?_⟩
      rw [iotaFun_last]
      apply Subtype.ext
      rw [tau_coe, tauR, min_eq_left (by linarith)]
      norm_num

/-- The pinch inclusion `iota : I^m → ∂I^{m+1}`, into the boundary subtype. -/
def iota (m : ℕ) (hm : 1 ≤ m) : C(IC m, ↥(Cube.boundary (Fin (m + 1)))) where
  toFun u := ⟨iotaFun m hm u, iotaFun_mem_boundary m hm u⟩
  continuous_toFun := Continuous.subtype_mk (continuous_iotaFun m hm) _

@[simp] theorem iota_coe (m : ℕ) (hm : 1 ≤ m) (u : IC m) :
    ((iota m hm u : ↥(Cube.boundary (Fin (m + 1)))) : IC (m + 1)) = iotaFun m hm u := rfl

/-- The pinch map `psi z = c + (1 - z_last/2) (initC z - c)`, `c` the centre of `I^m`. -/
def psiFun (m : ℕ) (z : IC (m + 1)) : IC m :=
  fun i => ⟨1/2 + (1 - (z (Fin.last m) : ℝ)/2) * ((z (Fin.castSucc i) : ℝ) - 1/2), by
    have hz1 : (z (Fin.last m) : ℝ) ≤ 1 := (z (Fin.last m)).2.2
    have hz0 : (0:ℝ) ≤ (z (Fin.last m) : ℝ) := (z (Fin.last m)).2.1
    have hx1 : (z (Fin.castSucc i) : ℝ) ≤ 1 := (z (Fin.castSucc i)).2.2
    have hx0 : (0:ℝ) ≤ (z (Fin.castSucc i) : ℝ) := (z (Fin.castSucc i)).2.1
    have hf0 : (0:ℝ) ≤ 1 - (z (Fin.last m) : ℝ)/2 := by linarith
    have hf1 : 1 - (z (Fin.last m) : ℝ)/2 ≤ 1 := by linarith
    have hxlo : -(1/2:ℝ) ≤ ((z (Fin.castSucc i) : ℝ) - 1/2) := by linarith
    have hxhi : ((z (Fin.castSucc i) : ℝ) - 1/2) ≤ 1/2 := by linarith
    constructor
    · have h := mul_nonneg hf0 (by linarith : (0:ℝ) ≤ ((z (Fin.castSucc i) : ℝ) - 1/2) + 1/2)
      have h2 : (1 - (z (Fin.last m) : ℝ)/2) / 2 ≤ 1/2 := by linarith
      nlinarith [h, mul_nonneg hf0 (by norm_num : (0:ℝ) ≤ 1/2)]
    · have h := mul_le_mul_of_nonneg_left hxhi hf0
      have h2 : (1 - (z (Fin.last m) : ℝ)/2) * (1/2) ≤ 1 * (1/2) := by
        nlinarith [hf1]
      nlinarith [h, h2]⟩

theorem continuous_psiFun (m : ℕ) : Continuous (psiFun m) := by
  refine continuous_pi fun i => Continuous.subtype_mk ?_ _
  have h1 : Continuous fun z : IC (m+1) => ((z (Fin.last m) : unitInterval) : ℝ) :=
    continuous_subtype_val.comp (continuous_apply _)
  have h2 : Continuous fun z : IC (m+1) => ((z (Fin.castSucc i) : unitInterval) : ℝ) :=
    continuous_subtype_val.comp (continuous_apply _)
  fun_prop

/-- The pinch map, as a continuous map `I^{m+1} → I^m`. -/
def psi (m : ℕ) : C(IC (m + 1), IC m) := ⟨psiFun m, continuous_psiFun m⟩

@[simp] theorem psi_apply (m : ℕ) (z : IC (m + 1)) : psi m z = psiFun m z := rfl

/-- The pinch map, restricted to the boundary subtype. -/
def psiBd (m : ℕ) : C(↥(Cube.boundary (Fin (m + 1))), IC m) :=
  (psi m).comp ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem psiBd_apply (m : ℕ) (z : ↥(Cube.boundary (Fin (m + 1)))) :
    psiBd m z = psiFun m z := rfl


/-! ## The `ℓ∞` radial coordinate of the first `m` coordinates of a point of `I^{m+1}` -/

/-- `sup_i |2 z_i - 1|` over the first `m` coordinates of `z : I^{m+1}`. -/
def sigT (m : ℕ) (hm : 1 ≤ m) (z : IC (m + 1)) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' (finNonempty hm)
    (fun i => |2 * ((z (Fin.castSucc i)) : ℝ) - 1|)

theorem sigT_le_one (m : ℕ) (hm : 1 ≤ m) (z : IC (m + 1)) : sigT m hm z ≤ 1 := by
  rw [sigT]
  refine Finset.sup'_le _ _ fun i _ => ?_
  have h0 : (0:ℝ) ≤ ((z (Fin.castSucc i)) : ℝ) := (z (Fin.castSucc i)).2.1
  have h1 : ((z (Fin.castSucc i)) : ℝ) ≤ 1 := (z (Fin.castSucc i)).2.2
  rw [abs_le]; constructor <;> linarith

theorem sigT_nonneg (m : ℕ) (hm : 1 ≤ m) (z : IC (m + 1)) : 0 ≤ sigT m hm z := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finNonempty hm)
    (fun i => |2 * ((z (Fin.castSucc i)) : ℝ) - 1|)
  rw [show sigT m hm z = _ from hi]; positivity

theorem sigT_eq_one_of_witness (m : ℕ) (hm : 1 ≤ m) (z : IC (m + 1))
    (h : ∃ j : Fin m, ((z (Fin.castSucc j)) : ℝ) = 0 ∨ ((z (Fin.castSucc j)) : ℝ) = 1) :
    sigT m hm z = 1 := by
  obtain ⟨j, hj⟩ := h
  refine le_antisymm (sigT_le_one m hm z) ?_
  have h2 : |2 * ((z (Fin.castSucc j)) : ℝ) - 1| = 1 := by
    rcases hj with h | h <;> rw [h] <;> norm_num
  calc (1:ℝ) = |2 * ((z (Fin.castSucc j)) : ℝ) - 1| := h2.symm
    _ ≤ sigT m hm z := by
        rw [sigT]
        exact (Finset.le_sup'_iff (finNonempty hm)).mpr ⟨j, Finset.mem_univ j, le_rfl⟩

theorem exists_castSucc_witness_of_mem_boundary (m : ℕ) {z : IC (m + 1)}
    (hz : z ∈ Cube.boundary (Fin (m + 1))) (h0 : z (Fin.last m) ≠ 0) (h1 : z (Fin.last m) ≠ 1) :
    ∃ j : Fin m, ((z (Fin.castSucc j)) : ℝ) = 0 ∨ ((z (Fin.castSucc j)) : ℝ) = 1 := by
  obtain ⟨i, hi⟩ := hz
  rcases hi with h | h
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact ⟨j, Or.inl (by rw [h]; rfl)⟩
    · exact absurd h h0
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact ⟨j, Or.inr (by rw [h]; rfl)⟩
    · exact absurd h h1

theorem f_nonneg (m : ℕ) (z : IC (m + 1)) :
    (0:ℝ) ≤ 1 - ((z (Fin.last m) : unitInterval) : ℝ)/2 := by
  have h1 : ((z (Fin.last m) : unitInterval) : ℝ) ≤ 1 := (z (Fin.last m)).2.2
  linarith

theorem f_ge_half (m : ℕ) (z : IC (m + 1)) :
    (1/2:ℝ) ≤ 1 - ((z (Fin.last m) : unitInterval) : ℝ)/2 := by
  have h1 : ((z (Fin.last m) : unitInterval) : ℝ) ≤ 1 := (z (Fin.last m)).2.2
  linarith

theorem sig_psiFun (m : ℕ) (hm : 1 ≤ m) (z : IC (m + 1)) :
    sig m hm (psiFun m z) = (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) * sigT m hm z := by
  have hf := f_nonneg m z
  refine le_antisymm ?_ ?_
  · rw [sig]
    refine Finset.sup'_le _ _ fun i _ => ?_
    have hxi : ((psiFun m z i : unitInterval) : ℝ)
        = 1/2 + (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) *
            (((z (Fin.castSucc i)) : ℝ) - 1/2) := rfl
    have hle : |2 * ((z (Fin.castSucc i)) : ℝ) - 1| ≤ sigT m hm z := by
      rw [sigT]
      exact (Finset.le_sup'_iff (finNonempty hm)).mpr ⟨i, Finset.mem_univ i, le_rfl⟩
    rw [hxi]
    have hkey : 2 * (1/2 + (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) *
          (((z (Fin.castSucc i)) : ℝ) - 1/2)) - 1
        = (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) * (2 * ((z (Fin.castSucc i)) : ℝ) - 1) := by
      ring
    rw [hkey, abs_mul, abs_of_nonneg hf]
    exact mul_le_mul_of_nonneg_left hle hf
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finNonempty hm)
      (fun i => |2 * ((z (Fin.castSucc i)) : ℝ) - 1|)
    have hxi : ((psiFun m z i : unitInterval) : ℝ)
        = 1/2 + (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) *
            (((z (Fin.castSucc i)) : ℝ) - 1/2) := rfl
    have hsig : |2 * ((psiFun m z i : unitInterval) : ℝ) - 1| ≤ sig m hm (psiFun m z) :=
      sig_le m hm _ i
    rw [show (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) * sigT m hm z
        = (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) *
            |2 * ((z (Fin.castSucc i)) : ℝ) - 1| from by rw [sigT, hi]]
    rw [hxi] at hsig
    have hkey : 2 * (1/2 + (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) *
          (((z (Fin.castSucc i)) : ℝ) - 1/2)) - 1
        = (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) * (2 * ((z (Fin.castSucc i)) : ℝ) - 1) := by
      ring
    rw [hkey, abs_mul, abs_of_nonneg hf] at hsig
    exact hsig

theorem max_sig_psiFun (m : ℕ) (hm : 1 ≤ m) {z : IC (m + 1)} (hz : z ∈ Cube.boundary (Fin (m + 1)))
    (h0 : z (Fin.last m) ≠ 0) :
    max (sig m hm (psiFun m z)) (1/2) = 1 - ((z (Fin.last m) : unitInterval) : ℝ)/2 := by
  rw [sig_psiFun]
  rcases eq_or_ne (z (Fin.last m)) 1 with h1 | h1
  · have hf1 : ((z (Fin.last m) : unitInterval) : ℝ) = 1 := congrArg Subtype.val h1
    rw [hf1]
    have hsT : sigT m hm z ≤ 1 := sigT_le_one m hm z
    have hle : (1 - (1:ℝ)/2) * sigT m hm z ≤ 1/2 := by nlinarith
    rw [max_eq_right hle]
    norm_num
  · have hsT : sigT m hm z = 1 :=
      sigT_eq_one_of_witness m hm z (exists_castSucc_witness_of_mem_boundary m hz h0 h1)
    rw [hsT, mul_one]
    exact max_eq_left (f_ge_half m z)

theorem tauR_psiFun (m : ℕ) (hm : 1 ≤ m) {z : IC (m + 1)} (hz : z ∈ Cube.boundary (Fin (m + 1)))
    (h0 : z (Fin.last m) ≠ 0) :
    tauR m hm (psiFun m z) = ((z (Fin.last m) : unitInterval) : ℝ) := by
  have hmx := max_sig_psiFun m hm hz h0
  have hf : (1:ℝ) - ((z (Fin.last m) : unitInterval) : ℝ)/2
      = max (sig m hm (psiFun m z)) (1/2) := hmx.symm
  rw [tauR]
  rcases le_or_gt ((1:ℝ)/2) (sig m hm (psiFun m z)) with hle | hlt
  · rw [max_eq_left hle] at hf
    rw [min_eq_right (by linarith)]
    linarith
  · rw [max_eq_right hlt.le] at hf
    rw [min_eq_left (by linarith)]
    linarith

theorem radialR_psiFun (m : ℕ) (hm : 1 ≤ m) {z : IC (m + 1)} (hz : z ∈ Cube.boundary (Fin (m + 1)))
    (h0 : z (Fin.last m) ≠ 0) (i : Fin m) :
    radialR m hm (psiFun m z) i = ((z (Fin.castSucc i)) : ℝ) := by
  have hmx := max_sig_psiFun m hm hz h0
  have hfi : ((psiFun m z i : unitInterval) : ℝ)
      = 1/2 + (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) *
          (((z (Fin.castSucc i)) : ℝ) - 1/2) := rfl
  rw [radialR, hfi, hmx]
  have hne : (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) ≠ 0 := by
    have := f_ge_half m z; linarith
  rw [show 1/2 + (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) *
        (((z (Fin.castSucc i)) : ℝ) - 1/2) - 1/2
      = (1 - ((z (Fin.last m) : unitInterval) : ℝ)/2) * (((z (Fin.castSucc i)) : ℝ) - 1/2) from by
    ring]
  rw [mul_div_cancel_left₀ _ hne]
  ring

theorem one_sub_tauR_half (m : ℕ) (hm : 1 ≤ m) (u : IC m) :
    1 - tauR m hm u / 2 = max (sig m hm u) (1/2) := by
  rw [tauR]
  rcases le_or_gt ((1:ℝ)/2) (sig m hm u) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h]
    ring
  · rw [min_eq_left (by linarith), max_eq_right h.le]
    norm_num

theorem psiFun_iotaFun (m : ℕ) (hm : 1 ≤ m) (u : IC m) : psiFun m (iotaFun m hm u) = u := by
  funext i
  apply Subtype.ext
  show 1/2 + (1 - ((iotaFun m hm u (Fin.last m) : unitInterval) : ℝ)/2) *
      (((iotaFun m hm u (Fin.castSucc i) : unitInterval) : ℝ) - 1/2) = ((u i : unitInterval) : ℝ)
  have h1 : ((iotaFun m hm u (Fin.last m) : unitInterval) : ℝ) = tauR m hm u := by
    rw [iotaFun_last]; rfl
  have h2 : ((iotaFun m hm u (Fin.castSucc i) : unitInterval) : ℝ) = radialR m hm u i := by
    rw [iotaFun_castSucc]; rfl
  rw [h1, h2, one_sub_tauR_half]
  have h3 : radialR m hm u i - 1/2
      = (((u i : unitInterval) : ℝ) - 1/2) / max (sig m hm u) (1/2) := by
    rw [radialR]; ring
  rw [show 1/2 + max (sig m hm u) (1/2) * (radialR m hm u i - 1/2)
      = 1/2 + max (sig m hm u) (1/2) *
          ((((u i : unitInterval) : ℝ) - 1/2) / max (sig m hm u) (1/2)) from by rw [h3]]
  have hM : max (sig m hm u) (1/2) ≠ 0 := ne_of_gt (lt_max_of_lt_right (by norm_num))
  rw [mul_div_cancel₀ _ hM]
  ring

end

end Work.RatHurewicz

import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase

/-!
# The horospherical (parabolic) subgroup of `O(n,1)` at a boundary point

For `ξ ∈ Sph n` put `θ = (ξ,1)` and `η = Jθ = (ξ,-1)`; these are null vectors with
`⟨θ,η⟩ = 2`, spanning a hyperbolic plane `V`, and the orthogonal complement `V^⊥` (positive
definite of dimension `n-1`) is the space in which the horospheres at `ξ` live.  Every
`M ∈ O(n,1)` fixing the null line `ℝθ` acts as a "horospherical similarity"

* `M θ = w θ`,
* `M η = η/w + s - (w ⟨s,s⟩/4) θ` with `s = π(Mη) ∈ V^⊥`,
* `M x = Q x` up to the `θ`-component, for `x ∈ V^⊥`,

and the parameters `(w,Q,s)` compose by `(w,Q,s)(w',Q',s') = (ww', QQ', s/w' + Q s')`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-! ## Elementary linear algebra of `ℝ^{Fin n ⊕ Fin 1}` -/

/-- Spatial part of a vector. -/
def hspat (x : Fin n ⊕ Fin 1 → ℝ) : E n := WithLp.toLp 2 (fun i => x (Sum.inl i))

/-- Time part of a vector. -/
def htime (x : Fin n ⊕ Fin 1 → ℝ) : ℝ := x (Sum.inr 0)

@[simp] lemma hspat_add (x y : Fin n ⊕ Fin 1 → ℝ) : hspat (x + y) = hspat x + hspat y := rfl
@[simp] lemma hspat_sub (x y : Fin n ⊕ Fin 1 → ℝ) : hspat (x - y) = hspat x - hspat y := rfl
@[simp] lemma hspat_smul (c : ℝ) (x : Fin n ⊕ Fin 1 → ℝ) : hspat (c • x) = c • hspat x := rfl
@[simp] lemma hspat_neg (x : Fin n ⊕ Fin 1 → ℝ) : hspat (-x) = -hspat x := rfl
@[simp] lemma htime_add (x y : Fin n ⊕ Fin 1 → ℝ) : htime (x + y) = htime x + htime y := rfl
@[simp] lemma htime_sub (x y : Fin n ⊕ Fin 1 → ℝ) : htime (x - y) = htime x - htime y := rfl
@[simp] lemma htime_smul (c : ℝ) (x : Fin n ⊕ Fin 1 → ℝ) : htime (c • x) = c * htime x := rfl
@[simp] lemma htime_neg (x : Fin n ⊕ Fin 1 → ℝ) : htime (-x) = -htime x := rfl

@[simp] lemma hspat_hlift' (u : E n) : hspat (hlift u) = u := rfl
@[simp] lemma htime_hlift' (u : E n) : htime (hlift u) = tpart u := rfl

/-- The Minkowski form in spatial/time coordinates. -/
lemma mform_eq (x y : Fin n ⊕ Fin 1 → ℝ) :
    mform x y = inner ℝ (hspat x) (hspat y) - htime x * htime y := by
  rw [mform_apply, inner_eq_sum]
  simp [hspat, htime]

lemma mform_add_left (x y z : Fin n ⊕ Fin 1 → ℝ) : mform (x + y) z = mform x z + mform y z := by
  simp only [mform_eq, hspat_add, htime_add, inner_add_left]
  ring

lemma mform_add_right (x y z : Fin n ⊕ Fin 1 → ℝ) : mform x (y + z) = mform x y + mform x z := by
  rw [mform_comm, mform_add_left, mform_comm (y := y), mform_comm (y := z)]

lemma mform_smul_left (c : ℝ) (x z : Fin n ⊕ Fin 1 → ℝ) : mform (c • x) z = c * mform x z := by
  have h : (starRingEnd ℝ) c = c := by simp
  simp only [mform_eq, hspat_smul, htime_smul, inner_smul_left, h]
  ring

lemma mform_smul_right (x : Fin n ⊕ Fin 1 → ℝ) (c : ℝ) (z : Fin n ⊕ Fin 1 → ℝ) :
    mform x (c • z) = c * mform x z := by
  rw [mform_comm, mform_smul_left, mform_comm]

lemma mform_sub_left (x y z : Fin n ⊕ Fin 1 → ℝ) : mform (x - y) z = mform x z - mform y z := by
  rw [sub_eq_add_neg, mform_add_left, show (-y : Fin n ⊕ Fin 1 → ℝ) = (-1 : ℝ) • y by simp,
    mform_smul_left]
  ring

lemma mform_neg_left (x z : Fin n ⊕ Fin 1 → ℝ) : mform (-x) z = - mform x z := by
  rw [show (-x : Fin n ⊕ Fin 1 → ℝ) = (-1 : ℝ) • x by simp, mform_smul_left]; ring

lemma mform_sub_right (x y z : Fin n ⊕ Fin 1 → ℝ) : mform x (y - z) = mform x y - mform x z := by
  rw [mform_comm, mform_sub_left, mform_comm (y := y), mform_comm (y := z)]

lemma mform_neg_right (x z : Fin n ⊕ Fin 1 → ℝ) : mform x (-z) = - mform x z := by
  rw [mform_comm, mform_neg_left, mform_comm]

/-! ## The two null vectors of a boundary point -/

/-- `η = J θ = (ξ,-1)`. -/
def horoEta (ξ : E n) : Fin n ⊕ Fin 1 → ℝ := Sum.elim (fun i => ξ i) (fun _ => -1)

@[simp] lemma hspat_horoEta (ξ : E n) : hspat (horoEta ξ) = ξ := rfl
@[simp] lemma htime_horoEta (ξ : E n) : htime (horoEta ξ) = -1 := rfl
@[simp] lemma hspat_theta (ξ : E n) : hspat (theta ξ) = ξ := rfl
@[simp] lemma htime_theta (ξ : E n) : htime (theta ξ) = 1 := rfl

lemma horoEta_eq_J (ξ : E n) :
    horoEta ξ = (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec (theta ξ) := by
  funext z
  rcases z with i | j
  · rw [pmOneMat_mulVec_inl]; rfl
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [pmOneMat_mulVec_inr]; rfl

lemma mform_theta_theta' (ξ : E n) : mform (theta ξ) (theta ξ) = ‖ξ‖ ^ 2 - 1 := by
  rw [mform_eq]; simp [real_inner_self_eq_norm_sq]

lemma mform_eta_eta (ξ : E n) : mform (horoEta ξ) (horoEta ξ) = ‖ξ‖ ^ 2 - 1 := by
  rw [mform_eq]; simp [real_inner_self_eq_norm_sq]

lemma mform_theta_eta (ξ : E n) : mform (theta ξ) (horoEta ξ) = ‖ξ‖ ^ 2 + 1 := by
  rw [mform_eq]; simp [real_inner_self_eq_norm_sq]

lemma mform_hlift_theta' (ξ : E n) (u : E n) :
    mform (hlift u) (theta ξ) = inner ℝ u ξ - tpart u := by
  rw [mform_eq]; simp

lemma mform_hlift_eta (ξ : E n) (u : E n) :
    mform (hlift u) (horoEta ξ) = inner ℝ u ξ + tpart u := by
  rw [mform_eq]; simp [add_comm]

lemma norm_sq_theta_eta (ξ : E n) (hξ : ξ ∈ Sph n) : ‖ξ‖ ^ 2 = 1 := by
  have := (mem_Sph_iff ξ).mp hξ
  rw [this]; norm_num

@[simp] lemma mform_theta_theta_sph (ξ : E n) (hξ : ξ ∈ Sph n) :
    mform (theta ξ) (theta ξ) = 0 := by
  rw [mform_theta_theta', norm_sq_theta_eta ξ hξ]; ring

@[simp] lemma mform_eta_eta_sph (ξ : E n) (hξ : ξ ∈ Sph n) :
    mform (horoEta ξ) (horoEta ξ) = 0 := by
  rw [mform_eta_eta, norm_sq_theta_eta ξ hξ]; ring

@[simp] lemma mform_theta_eta_sph (ξ : E n) (hξ : ξ ∈ Sph n) :
    mform (theta ξ) (horoEta ξ) = 2 := by
  rw [mform_theta_eta, norm_sq_theta_eta ξ hξ]; norm_num

@[simp] lemma mform_eta_theta_sph (ξ : E n) (hξ : ξ ∈ Sph n) :
    mform (horoEta ξ) (theta ξ) = 2 := by
  rw [mform_comm, mform_theta_eta_sph ξ hξ]

/-- `exp (busemann ξ u) = -⟨hlift u, θ⟩`. -/
lemma exp_busemann_eq_neg_mform (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) :
    Real.exp (busemann ξ u) = - mform (hlift u) (theta ξ) := by
  have hpos : 0 < tpart u - inner ℝ u ξ := busemann_arg_pos ξ hξ u
  rw [busemann_eq_log, Real.exp_log hpos, mform_hlift_theta']
  ring

/-- `hlift 0 = (θ - η)/2`. -/
lemma hlift_zero_eq (ξ : E n) : hlift (0 : E n) = (1/2 : ℝ) • (theta ξ - horoEta ξ) := by
  ext z
  rcases z with i | j
  · simp [hlift, theta, horoEta]
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    norm_num [hlift, theta, horoEta, tpart]

/-! ## The orthogonal projection onto `V^⊥` -/

/-- The projection onto `V^⊥ = {x | ⟨x,θ⟩ = 0, ⟨x,η⟩ = 0}` along `span{θ,η}`. -/
def horoProj (ξ : E n) (x : Fin n ⊕ Fin 1 → ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  x - (mform x (theta ξ) / 2) • horoEta ξ - (mform x (horoEta ξ) / 2) • theta ξ

lemma horoProj_add (ξ : E n) (x y : Fin n ⊕ Fin 1 → ℝ) :
    horoProj ξ (x + y) = horoProj ξ x + horoProj ξ y := by
  simp only [horoProj, mform_add_left, mform_add_right]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, horoEta, theta, Sum.elim_inl,
    Sum.elim_inr]
  ring

lemma horoProj_smul (ξ : E n) (c : ℝ) (x : Fin n ⊕ Fin 1 → ℝ) :
    horoProj ξ (c • x) = c • horoProj ξ x := by
  simp only [horoProj, mform_smul_left, mform_smul_right]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, horoEta, theta, Sum.elim_inl, Sum.elim_inr]
  ring

lemma horoProj_neg (ξ : E n) (x : Fin n ⊕ Fin 1 → ℝ) : horoProj ξ (-x) = - horoProj ξ x := by
  rw [show (-x : Fin n ⊕ Fin 1 → ℝ) = (-1 : ℝ) • x by simp, horoProj_smul]
  simp

lemma horoProj_sub (ξ : E n) (x y : Fin n ⊕ Fin 1 → ℝ) :
    horoProj ξ (x - y) = horoProj ξ x - horoProj ξ y := by
  rw [sub_eq_add_neg, horoProj_add, horoProj_neg, sub_eq_add_neg]

/-- The decomposition `x = π x + a θ + b η`. -/
lemma horoProj_decomp (ξ : E n) (x : Fin n ⊕ Fin 1 → ℝ) :
    horoProj ξ x + (mform x (theta ξ) / 2) • horoEta ξ + (mform x (horoEta ξ) / 2) • theta ξ = x := by
  ext i
  simp only [horoProj, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, horoEta, theta,
    Sum.elim_inl, Sum.elim_inr]
  ring

lemma mform_horoProj_theta (ξ : E n) (hξ : ξ ∈ Sph n) (x : Fin n ⊕ Fin 1 → ℝ) :
    mform (horoProj ξ x) (theta ξ) = 0 := by
  simp only [horoProj, mform_sub_left, mform_smul_left, mform_theta_theta_sph ξ hξ,
    mform_eta_theta_sph ξ hξ]
  ring

lemma mform_horoProj_eta (ξ : E n) (hξ : ξ ∈ Sph n) (x : Fin n ⊕ Fin 1 → ℝ) :
    mform (horoProj ξ x) (horoEta ξ) = 0 := by
  simp only [horoProj, mform_sub_left, mform_smul_left, mform_theta_eta_sph ξ hξ,
    mform_eta_eta_sph ξ hξ]
  ring

lemma horoProj_idem (ξ : E n) (hξ : ξ ∈ Sph n) (x : Fin n ⊕ Fin 1 → ℝ) :
    horoProj ξ (horoProj ξ x) = horoProj ξ x := by
  have h1 := mform_horoProj_theta ξ hξ x
  have h2 := mform_horoProj_eta ξ hξ x
  rw [show horoProj ξ (horoProj ξ x)
      = horoProj ξ x - (mform (horoProj ξ x) (theta ξ) / 2) • horoEta ξ
          - (mform (horoProj ξ x) (horoEta ξ) / 2) • theta ξ from rfl, h1, h2]
  simp

lemma horoProj_theta (ξ : E n) (hξ : ξ ∈ Sph n) : horoProj ξ (theta ξ) = 0 := by
  simp only [horoProj, mform_theta_theta_sph ξ hξ, mform_theta_eta_sph ξ hξ]
  ext i
  simp only [Pi.sub_apply, Pi.zero_apply, zero_div, zero_smul, sub_zero, Pi.smul_apply, one_smul]
  ring

lemma horoProj_eta (ξ : E n) (hξ : ξ ∈ Sph n) : horoProj ξ (horoEta ξ) = 0 := by
  simp only [horoProj, mform_eta_theta_sph ξ hξ, mform_eta_eta_sph ξ hξ]
  ext i
  simp only [Pi.sub_apply, Pi.zero_apply, zero_div, zero_smul, sub_zero, Pi.smul_apply, one_smul]
  ring

/-- A vector of `V^⊥` has zero time coordinate. -/
lemma htime_eq_zero_of_horoProj (ξ : E n) (hξ : ξ ∈ Sph n) {x : Fin n ⊕ Fin 1 → ℝ}
    (hx : horoProj ξ x = x) : htime x = 0 := by
  have h1 : mform x (theta ξ) = 0 := by rw [← hx]; exact mform_horoProj_theta ξ hξ x
  have h2 : mform x (horoEta ξ) = 0 := by rw [← hx]; exact mform_horoProj_eta ξ hξ x
  rw [mform_eq] at h1 h2
  simp only [hspat_theta, htime_theta, mul_one, sub_eq_add_neg] at h1
  simp only [hspat_horoEta, htime_horoEta, mul_neg, mul_one, sub_neg_eq_add] at h2
  linarith

/-- On `V^⊥` the Minkowski form is the Euclidean form of the spatial part. -/
lemma mform_eq_norm_sq_of_horoProj (ξ : E n) (hξ : ξ ∈ Sph n) {x : Fin n ⊕ Fin 1 → ℝ}
    (hx : horoProj ξ x = x) : mform x x = ‖hspat x‖ ^ 2 := by
  rw [mform_eq, htime_eq_zero_of_horoProj ξ hξ hx]
  simp

/-- The "norm" on `V^⊥` (Euclidean norm of the spatial part). -/
def vnorm (x : Fin n ⊕ Fin 1 → ℝ) : ℝ := ‖hspat x‖

lemma mform_eq_inner_of_horoProj (ξ : E n) (hξ : ξ ∈ Sph n) {x y : Fin n ⊕ Fin 1 → ℝ}
    (hx : horoProj ξ x = x) (hy : horoProj ξ y = y) :
    mform x y = inner ℝ (hspat x) (hspat y) := by
  rw [mform_eq, htime_eq_zero_of_horoProj ξ hξ hx, htime_eq_zero_of_horoProj ξ hξ hy]
  simp

/-! ## The normal form of a matrix fixing the null line of `θ` -/

/-- `M` is `J`-orthogonal, i.e. an element of `O(n,1)`. -/
def IsJOrth (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) : Prop :=
  Mᵀ * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * M
    = (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ))

lemma mform_mulVec_mulVec {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ} (hM : IsJOrth M)
    (x y : Fin n ⊕ Fin 1 → ℝ) : mform (M *ᵥ x) (M *ᵥ y) = mform x y :=
  Submission.Mostow.Hyper.mink_mulVec M (by simpa [IsJOrth, Matrix.transpose] using hM) x y

/-- swapped orthogonality statements -/
lemma mform_theta_horoProj (ξ : E n) (hξ : ξ ∈ Sph n) (x : Fin n ⊕ Fin 1 → ℝ) :
    mform (theta ξ) (horoProj ξ x) = 0 := by
  rw [mform_comm, mform_horoProj_theta ξ hξ]

lemma mform_eta_horoProj (ξ : E n) (hξ : ξ ∈ Sph n) (x : Fin n ⊕ Fin 1 → ℝ) :
    mform (horoEta ξ) (horoProj ξ x) = 0 := by
  rw [mform_comm, mform_horoProj_eta ξ hξ]

/-- The algebraic core of the normal form. -/
lemma parab_eta_aux (ξ : E n) (hξ : ξ ∈ Sph n) {Y : Fin n ⊕ Fin 1 → ℝ} {w : ℝ} (hw0 : w ≠ 0)
    (h1 : mform Y (theta ξ) = 2 / w) (h2 : mform Y Y = 0) :
    Y = (1 / w) • horoEta ξ + horoProj ξ Y
          - (w * mform (horoProj ξ Y) (horoProj ξ Y) / 4) • theta ξ := by
  have hb : mform Y (theta ξ) / 2 = 1 / w := by rw [h1]; field_simp
  have hsplit : mform Y Y = mform (horoProj ξ Y) (horoProj ξ Y)
      + 4 * ((mform Y (theta ξ) / 2) * (mform Y (horoEta ξ) / 2)) := by
    conv_lhs => rw [← horoProj_decomp ξ Y]
    simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right,
      mform_horoProj_theta ξ hξ Y, mform_horoProj_eta ξ hξ Y, mform_theta_horoProj ξ hξ Y,
      mform_eta_horoProj ξ hξ Y, mform_theta_theta_sph ξ hξ, mform_eta_eta_sph ξ hξ,
      mform_theta_eta_sph ξ hξ, mform_eta_theta_sph ξ hξ]
    ring
  have ha : mform Y (horoEta ξ) / 2 = -(w * mform (horoProj ξ Y) (horoProj ξ Y) / 4) := by
    rw [h2, hb] at hsplit
    field_simp at hsplit ⊢
    linarith
  calc Y = horoProj ξ Y + (mform Y (theta ξ) / 2) • horoEta ξ
        + (mform Y (horoEta ξ) / 2) • theta ξ := (horoProj_decomp ξ Y).symm
    _ = (1 / w) • horoEta ξ + horoProj ξ Y
          - (w * mform (horoProj ξ Y) (horoProj ξ Y) / 4) • theta ξ := by
        rw [hb, ha]; module

/-- The `η`-row of the normal form: `M η = η/w + s - (w⟨s,s⟩/4) θ`. -/
theorem O1_parab_eta (ξ : E n) (hξ : ξ ∈ Sph n) {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ}
    (hO : IsJOrth M) {w : ℝ} (hw : M *ᵥ theta ξ = w • theta ξ) (hw0 : w ≠ 0) :
    M *ᵥ horoEta ξ
      = (1 / w) • horoEta ξ + horoProj ξ (M *ᵥ horoEta ξ)
          - (w * mform (horoProj ξ (M *ᵥ horoEta ξ)) (horoProj ξ (M *ᵥ horoEta ξ)) / 4) • theta ξ := by
  have h1 : mform (M *ᵥ horoEta ξ) (theta ξ) = 2 / w := by
    have h := mform_mulVec_mulVec hO (horoEta ξ) (theta ξ)
    rw [hw, mform_eta_theta_sph ξ hξ, mform_smul_right] at h
    field_simp at h ⊢
    linarith
  have h2 : mform (M *ᵥ horoEta ξ) (M *ᵥ horoEta ξ) = 0 := by
    have h := mform_mulVec_mulVec hO (horoEta ξ) (horoEta ξ)
    rw [mform_eta_eta_sph ξ hξ] at h
    exact h
  exact parab_eta_aux ξ hξ hw0 h1 h2

/-- The "rotation part" of `M` acting on `V^⊥`. -/
def parabQ (ξ : E n) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (x : Fin n ⊕ Fin 1 → ℝ) : Fin n ⊕ Fin 1 → ℝ := horoProj ξ (M *ᵥ x)

/-- `Q` preserves the Minkowski form on `V^⊥`. -/
lemma parabQ_isom (ξ : E n) (hξ : ξ ∈ Sph n) {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ}
    (hO : IsJOrth M) {w : ℝ} (hw : M *ᵥ theta ξ = w • theta ξ) (hw0 : w ≠ 0)
    {x y : Fin n ⊕ Fin 1 → ℝ} (hx : horoProj ξ x = x) (hy : horoProj ξ y = y) :
    mform (parabQ ξ M x) (parabQ ξ M y) = mform x y := by
  have hxθ : mform x (theta ξ) = 0 := by rw [← hx]; exact mform_horoProj_theta ξ hξ x
  have hyθ : mform y (theta ξ) = 0 := by rw [← hy]; exact mform_horoProj_theta ξ hξ y
  have hMxθ : mform (M *ᵥ x) (theta ξ) = 0 := by
    have h := mform_mulVec_mulVec hO x (theta ξ)
    rw [hw, mform_smul_right, hxθ] at h
    exact (mul_eq_zero.mp (by linarith [h] : w * mform (M *ᵥ x) (theta ξ) = 0)).resolve_left hw0
  have hMyθ : mform (M *ᵥ y) (theta ξ) = 0 := by
    have h := mform_mulVec_mulVec hO y (theta ξ)
    rw [hw, mform_smul_right, hyθ] at h
    exact (mul_eq_zero.mp (by linarith [h] : w * mform (M *ᵥ y) (theta ξ) = 0)).resolve_left hw0
  have hdecx : M *ᵥ x = horoProj ξ (M *ᵥ x) + (mform (M *ᵥ x) (horoEta ξ) / 2) • theta ξ := by
    have h := horoProj_decomp ξ (M *ᵥ x)
    rw [hMxθ] at h
    simpa using h.symm
  have hdecy : M *ᵥ y = horoProj ξ (M *ᵥ y) + (mform (M *ᵥ y) (horoEta ξ) / 2) • theta ξ := by
    have h := horoProj_decomp ξ (M *ᵥ y)
    rw [hMyθ] at h
    simpa using h.symm
  change mform (horoProj ξ (M *ᵥ x)) (horoProj ξ (M *ᵥ y)) = mform x y
  have hpres := mform_mulVec_mulVec hO x y
  rw [hdecx, hdecy] at hpres
  simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right,
    mform_horoProj_theta ξ hξ (M *ᵥ x), mform_horoProj_theta ξ hξ (M *ᵥ y),
    mform_theta_horoProj ξ hξ (M *ᵥ x), mform_theta_horoProj ξ hξ (M *ᵥ y),
    mform_theta_theta_sph ξ hξ, mform_theta_eta_sph ξ hξ] at hpres
  ring_nf at hpres
  exact hpres

/-- Composition of the normal-form parameters in the `η`-coordinate. -/
lemma horoProj_mulVec_eta_comp (ξ : E n) (hξ : ξ ∈ Sph n)
    {M M' : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ} (hO' : IsJOrth M')
    {w w' : ℝ} (hw : M *ᵥ theta ξ = w • theta ξ) (hw' : M' *ᵥ theta ξ = w' • theta ξ)
    (hw0' : w' ≠ 0) :
    horoProj ξ ((M * M') *ᵥ horoEta ξ)
      = (1 / w') • horoProj ξ (M *ᵥ horoEta ξ)
        + horoProj ξ (M *ᵥ horoProj ξ (M' *ᵥ horoEta ξ)) := by
  have hnf := O1_parab_eta ξ hξ hO' hw' hw0'
  have hk : horoProj ξ ((w' * mform (horoProj ξ (M' *ᵥ horoEta ξ))
        (horoProj ξ (M' *ᵥ horoEta ξ)) / 4) • (w • theta ξ)) = 0 := by
    rw [horoProj_smul, horoProj_smul, horoProj_theta ξ hξ, smul_zero, smul_zero]
  conv_lhs => rw [← Matrix.mulVec_mulVec, hnf, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hw, horoProj_sub, horoProj_add, horoProj_smul,
    hk, sub_zero]

/-- The cosh-kernel of `M e₀` with `e₀ = hlift 0`, computed via the time coordinate. -/
lemma mform_mulVec_hlift_zero (ξ : E n) (hξ : ξ ∈ Sph n)
    {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ}
    (hO : IsJOrth M) {w : ℝ} (hw : M *ᵥ theta ξ = w • theta ξ) (hw0 : w ≠ 0) :
    mform (M *ᵥ hlift 0) (hlift 0)
      = -(w / 2 + 1 / (2 * w)
          + w * mform (horoProj ξ (M *ᵥ horoEta ξ)) (horoProj ξ (M *ᵥ horoEta ξ)) / 8) := by
  have hnf := O1_parab_eta ξ hξ hO hw hw0
  have hs0 : htime (horoProj ξ (M *ᵥ horoEta ξ)) = 0 :=
    htime_eq_zero_of_horoProj ξ hξ (horoProj_idem ξ hξ (M *ᵥ horoEta ξ))
  have hmain : htime (M *ᵥ hlift 0)
      = (w + 1 / w
          + w * mform (horoProj ξ (M *ᵥ horoEta ξ)) (horoProj ξ (M *ᵥ horoEta ξ)) / 4) / 2 := by
    conv_lhs => rw [hlift_zero_eq ξ, Matrix.mulVec_smul, Matrix.mulVec_sub, hw, hnf]
    simp only [htime_smul, htime_add, htime_sub, htime_theta, htime_horoEta, hs0]
    ring
  conv_lhs => rw [mform_eq, hspat_hlift', htime_hlift', tpart_zero, inner_zero_right, zero_sub,
    mul_one, hmain]
  ring


/-- Adjointness of `mform` with respect to `Matrix.mulVec` (the adjoint is `J Aᵀ J`). -/
lemma mform_mulVec_left (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (x y : Fin n ⊕ Fin 1 → ℝ) :
    mform (A *ᵥ x) y
      = mform x (((pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * Aᵀ
          * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ))) *ᵥ y) := by
  simp only [mform]
  conv_lhs => rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [← mul_assoc, ← mul_assoc, pmOneMat_mul_pmOneMat, one_mul]

@[simp] lemma mform_zero_left (y : Fin n ⊕ Fin 1 → ℝ) : mform (0 : Fin n ⊕ Fin 1 → ℝ) y = 0 := by
  simp [mform]

@[simp] lemma mform_zero_right (x : Fin n ⊕ Fin 1 → ℝ) : mform x (0 : Fin n ⊕ Fin 1 → ℝ) = 0 := by
  simp [mform]

/-- The chart vectors `hlift u` span `ℝ^{Fin n ⊕ Fin 1}`. -/
lemma hlift_span_top : Submodule.span ℝ (Set.range (hlift : E n → Fin n ⊕ Fin 1 → ℝ)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hspatial : ∀ v : E n, (Sum.elim (fun i => v i) (fun _ => (0 : ℝ)) : Fin n ⊕ Fin 1 → ℝ)
      ∈ Submodule.span ℝ (Set.range (hlift : E n → Fin n ⊕ Fin 1 → ℝ)) := by
    intro v
    have hcomb : (Sum.elim (fun i => v i) (fun _ => (0 : ℝ)) : Fin n ⊕ Fin 1 → ℝ)
        = (1 / 2 : ℝ) • (hlift v - hlift (-v)) := by
      ext z; rcases z with k | k
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hlift, Sum.elim_inl, hspat,
          Pi.neg_apply, WithLp.ofLp_neg, WithLp.ofLp_toLp]
        ring
      · obtain rfl : k = 0 := Subsingleton.elim _ _
        simp [hlift, tpart, norm_neg]
    rw [hcomb]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨v, rfl⟩)
      (Submodule.subset_span ⟨-v, rfl⟩))
  have hx : x = (Sum.elim (fun i => hspat x i) (fun _ => (0 : ℝ)) : Fin n ⊕ Fin 1 → ℝ)
      + (htime x) • hlift (0 : E n) := by
    ext z; rcases z with k | k
    · simp [hspat, hlift]
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      simp [hlift, htime, tpart]
  rw [hx]
  exact Submodule.add_mem _ (hspatial (hspat x)) (Submodule.smul_mem _ _
    (Submodule.subset_span ⟨0, rfl⟩))

/-- The standard basis vector evaluated against a vector. -/
lemma single_dotProduct' (j : Fin n ⊕ Fin 1) (v : Fin n ⊕ Fin 1 → ℝ) :
    (Pi.single j (1 : ℝ)) ⬝ᵥ v = v j := by
  rw [dotProduct, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp only [Pi.single_apply, Pi.zero_apply, if_neg hb, zero_mul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- A vector is determined by all its `mform`-pairings with the chart points `hlift u`. -/
lemma eq_of_forall_mform_hlift {a b : Fin n ⊕ Fin 1 → ℝ}
    (h : ∀ u : E n, mform (hlift u) a = mform (hlift u) b) : a = b := by
  have hall : ∀ x : Fin n ⊕ Fin 1 → ℝ, mform x a = mform x b := by
    let S : Submodule ℝ (Fin n ⊕ Fin 1 → ℝ) :=
      { carrier := {x | mform x a = mform x b}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq, mform_add_left]
          rw [hx, hy]
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_setOf_eq, mform_smul_left]
          rw [hx] }
    have hsub : Submodule.span ℝ (Set.range (hlift : E n → Fin n ⊕ Fin 1 → ℝ)) ≤ S := by
      rw [Submodule.span_le]
      rintro y ⟨u, rfl⟩
      exact h u
    intro x
    exact hsub (by rw [hlift_span_top]; trivial)
  have h2 : ∀ j : Fin n ⊕ Fin 1,
      ((pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec a) j
        = ((pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec b) j := by
    intro j
    have h3 := hall (Pi.single j (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)
    rw [mform, mform, single_dotProduct', single_dotProduct'] at h3
    exact h3
  have h4 : (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec a
      = (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec b := funext h2
  have h5 := congrArg (fun v => (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec v) h4
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, pmOneMat_mul_pmOneMat] at h5
  simpa using h5


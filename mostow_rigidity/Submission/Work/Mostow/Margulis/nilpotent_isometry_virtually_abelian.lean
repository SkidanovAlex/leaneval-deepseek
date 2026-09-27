import Mathlib
import Submission.Work.Mostow.Margulis.fg_nilpotent_orthogonal_virtually_abelian

namespace Work.Mostow.Margulis

/-!
# Nilpotent groups of Euclidean isometries are virtually abelian

Let `G ≤ Isom(V)` be a finitely generated nilpotent group of isometries of a finite-dimensional
real inner product space `V`, acting properly discontinuously.  Then `G` has a finite-index
abelian subgroup.

The proof is elementary once one knows that the group of linear parts is virtually abelian
(the classical `Zassenhaus` / compact-Lie fact, here `fg_nilpotent_orthogonal_virtually_abelian`):

* every translation in `G` is central (`isoLin_eq_one_mem_center`): the iterated commutators of a
translation `t = (1,u)` with `s = (A,a)` are the translations by `(1-A)^k u`, hence in the
`k`-th term of the lower central series, so `(1-A)^k u = 0` for some `k`; since `A` is orthogonal
this forces `(1-A)u = 0`;
* if a finite-index subgroup `G₁ ≤ G` has pairwise commuting linear parts, then `G₁` is abelian
(`comm_of_commuting_isoLin`): for `a, b ∈ G₁` the commutator `⁅a,b⁆` has trivial linear part,
hence is central, hence its translation part `w` is fixed by the linear parts of `a` and `b`,
while the explicit commutator formula exhibits `w` as `(A-1)(v_b) - (B-1)(v_a)`, which is
orthogonal to `w`; so `w = 0`.
-/

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]


def isoLin (f : V ≃ᵢ V) : V ≃ₗᵢ[ℝ] V := f.toRealLinearIsometryEquiv
def isoTr (f : V ≃ᵢ V) : V := f 0

lemma isoLin_apply (f : V ≃ᵢ V) (x : V) : isoLin f x = f x - isoTr f := by
  rw [isoLin, isoTr, IsometryEquiv.toRealLinearIsometryEquiv_apply]

lemma iso_apply_eq (f : V ≃ᵢ V) (x : V) : f x = isoLin f x + isoTr f := by
  rw [isoLin_apply]; abel

@[simp] lemma isoTr_one : isoTr (1 : V ≃ᵢ V) = 0 := rfl

@[simp] lemma isoLin_one : isoLin (1 : V ≃ᵢ V) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  have h := iso_apply_eq (1 : V ≃ᵢ V) x
  rw [show (1 : V ≃ᵢ V) x = x from rfl, isoTr_one, add_zero] at h
  exact h.symm

/-- the identity linear isometry is the identity function -/
@[simp] lemma one_lin_apply (x : V) : (1 : V ≃ₗᵢ[ℝ] V) x = x := rfl

lemma isoTr_mul (f g : V ≃ᵢ V) : isoTr (f * g) = isoLin f (isoTr g) + isoTr f := by
  rw [isoTr, IsometryEquiv.mul_apply, iso_apply_eq g, iso_apply_eq f, map_add, map_zero, map_zero,
    zero_add]

lemma isoLin_mul (f g : V ≃ᵢ V) : isoLin (f * g) = isoLin f * isoLin g := by
  apply LinearIsometryEquiv.ext
  intro x
  rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
  have h := iso_apply_eq (f * g) x
  rw [IsometryEquiv.mul_apply, iso_apply_eq g x, iso_apply_eq f, map_add, isoTr_mul,
    add_assoc] at h
  exact (add_right_cancel h).symm

lemma isoLin_inv (f : V ≃ᵢ V) : isoLin f⁻¹ = (isoLin f)⁻¹ := by
  have h := isoLin_mul f f⁻¹
  rw [mul_inv_cancel, isoLin_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma isoTr_inv (f : V ≃ᵢ V) : isoTr f⁻¹ = -(isoLin f)⁻¹ (isoTr f) := by
  have h := isoTr_mul f f⁻¹
  rw [mul_inv_cancel, isoTr_one] at h
  have h2 : isoLin f (isoTr f⁻¹) = - isoTr f := eq_neg_of_add_eq_zero_left h.symm
  calc isoTr f⁻¹ = (isoLin f)⁻¹ (isoLin f (isoTr f⁻¹)) := by simp
    _ = (isoLin f)⁻¹ (-(isoTr f)) := by rw [h2]
    _ = - (isoLin f)⁻¹ (isoTr f) := by rw [map_neg]

lemma isoTr_comm_gen (f g : V ≃ᵢ V) :
    isoTr (f * g * f⁻¹ * g⁻¹)
      = -(isoLin f * isoLin g * (isoLin f)⁻¹ * (isoLin g)⁻¹) (isoTr g)
          - (isoLin f * isoLin g * (isoLin f)⁻¹) (isoTr f) + isoLin f (isoTr g) + isoTr f := by
  simp only [isoTr_mul, isoTr_inv, isoLin_mul, isoLin_inv, LinearIsometryEquiv.mul_def,
    LinearIsometryEquiv.trans_apply, map_add, map_neg]
  abel

lemma isoLin_comm (f g : V ≃ᵢ V) :
    isoLin (f * g * f⁻¹ * g⁻¹)
      = isoLin f * isoLin g * (isoLin f)⁻¹ * (isoLin g)⁻¹ := by
  rw [isoLin_mul, isoLin_mul, isoLin_mul, isoLin_inv, isoLin_inv]

/-- commutator with a translation -/
lemma isoTr_comm_translation (t g : V ≃ᵢ V) (ht : isoLin t = 1) :
    isoTr (t * g * t⁻¹ * g⁻¹) = isoTr t - isoLin g (isoTr t) := by
  rw [isoTr_comm_gen, ht]
  simp only [one_mul, inv_one, one_lin_apply, LinearIsometryEquiv.mul_def,
    LinearIsometryEquiv.trans_apply]
  simp
  abel

/-- commutator of two isometries with commuting linear parts -/
lemma isoTr_comm_commuting (f g : V ≃ᵢ V) (h : isoLin f * isoLin g = isoLin g * isoLin f) :
    isoTr (f * g * f⁻¹ * g⁻¹)
      = (isoLin f (isoTr g) - isoTr g) - (isoLin g (isoTr f) - isoTr f) := by
  rw [isoTr_comm_gen, h]
  have h1 : isoLin g * isoLin f * (isoLin f)⁻¹ * (isoLin g)⁻¹ = 1 := by group
  have h2 : isoLin g * isoLin f * (isoLin f)⁻¹ = isoLin g := by group
  rw [h1, h2]
  simp only [one_lin_apply, LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply,
    map_sub]
  abel

/-- an isometry with trivial linear part and trivial translation part is the identity -/
lemma iso_eq_one_of (f : V ≃ᵢ V) (h1 : isoLin f = 1) (h2 : isoTr f = 0) : f = 1 := by
  apply IsometryEquiv.ext
  intro x
  rw [iso_apply_eq, h1, one_lin_apply, h2, add_zero]
  rfl





open scoped commutatorElement

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

lemma lin_sub_sq_eq_zero (A : V ≃ₗᵢ[ℝ] V) (w : V) :
    ((1 : V →L[ℝ] V) - (A : V →L[ℝ] V))
      (((1 : V →L[ℝ] V) - (A : V →L[ℝ] V)) w) = 0 →
    ((1 : V →L[ℝ] V) - (A : V →L[ℝ] V)) w = 0 := by
  intro h
  set N : V →L[ℝ] V := (1 : V →L[ℝ] V) - (A : V →L[ℝ] V) with hN
  have hNapp : ∀ z : V, N z = z - A z := by
    intro z
    rw [hN, sub_apply]
    rfl
  have h' : N (N w) = 0 := h
  have h2 : N w - A (N w) = 0 := by
    rw [← hNapp (N w)]
    exact h'
  have hAv : A (N w) = N w := (sub_eq_zero.mp h2).symm
  have hAinv : A.symm (N w) = N w := by
    have h4 : A.symm (A (N w)) = N w := LinearIsometryEquiv.symm_apply_apply A (N w)
    rwa [hAv] at h4
  have hinner : inner ℝ (N w) (N w) = 0 := by
    have h3 : inner ℝ (N w) (N w) = inner ℝ (N w) w - inner ℝ (N w) (A w) := by
      have hw : N w = w - A w := hNapp w
      rw [hw, inner_sub_right, inner_sub_left]
    have h4 : inner ℝ (N w) (A w) = inner ℝ (N w) w := by
      have h5 := LinearIsometryEquiv.inner_map_map A (A⁻¹ (N w)) w
      rw [show A (A⁻¹ (N w)) = N w from LinearIsometryEquiv.apply_symm_apply A (N w),
        show A⁻¹ (N w) = N w from hAinv] at h5
      exact h5
    rw [h3, h4, sub_self]
  have := inner_self_eq_zero.mp hinner
  rwa [hN] at this

lemma lin_sub_pow_eq_zero (A : V ≃ₗᵢ[ℝ] V) (n : ℕ) (u : V)
    (h : (((1 : V →L[ℝ] V) - (A : V →L[ℝ] V)) ^ n) u = 0) :
    ((1 : V →L[ℝ] V) - (A : V →L[ℝ] V)) u = 0 := by
  set N : V →L[ℝ] V := (1 : V →L[ℝ] V) - (A : V →L[ℝ] V) with hN
  have hmul : ∀ a b : V →L[ℝ] V, ∀ z : V, (a * b) z = a (b z) := fun a b z =>
    ContinuousLinearMap.mul_apply a b z
  have hpowsucc : ∀ (n : ℕ), (N ^ (n + 1)) = N * (N ^ n) := fun n => pow_succ' N n
  have step : ∀ (k : ℕ) (w : V), (N ^ (k + 2)) w = 0 → (N ^ (k + 1)) w = 0 := by
    intro k w hw
    have h1 : (N ^ (k + 2)) w = N (N ((N ^ k) w)) := by
      simp only [hpowsucc, hmul]
    have h2 : N (N ((N ^ k) w)) = 0 := by rw [← h1]; exact hw
    have h3 : N ((N ^ k) w) = 0 := lin_sub_sq_eq_zero A ((N ^ k) w) h2
    have h4 : (N ^ (k + 1)) w = N ((N ^ k) w) := by
      rw [show (N ^ (k + 1)) = N * (N ^ k) from hpowsucc k, hmul]
    rw [h4]; exact h3
  have key : ∀ (n : ℕ) (w : V), (N ^ n) w = 0 → N w = 0 := by
    intro n
    induction n with
    | zero =>
      intro w hw
      have hw' : w = 0 := by simpa using hw
      rw [hw', map_zero]
    | succ n ih =>
      intro w hw
      rcases n with _ | n
      · simpa using hw
      · exact ih w (step n w hw)
  have := key n u h
  rwa [hN] at this



open scoped commutatorElement

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The kernel of `isoLin` is central (in a nilpotent group of isometries). -/
lemma isoLin_eq_one_mem_center (G : Subgroup (V ≃ᵢ V)) (hnil : Group.IsNilpotent G)
    (t : G) (ht : isoLin ((t : G) : V ≃ᵢ V) = 1) : t ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro s
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  set A : V →L[ℝ] V := (isoLin ((s : G) : V ≃ᵢ V) : V →L[ℝ] V) with hA
  set N : V →L[ℝ] V := (1 : V →L[ℝ] V) - A with hN
  set u : V := isoTr ((t : G) : V ≃ᵢ V) with hu
  set c : ℕ → G := fun k => Nat.rec t (fun _ ck => ⁅ck, s⁆) k with hc
  have hc0 : c 0 = t := rfl
  have hcs : ∀ k, c (k + 1) = ⁅c k, s⁆ := fun k => rfl
  have hcoe : ∀ k, ((c (k + 1) : G) : V ≃ᵢ V)
      = ((c k : G) : V ≃ᵢ V) * ((s : G) : V ≃ᵢ V)
        * (((c k : G) : V ≃ᵢ V))⁻¹ * (((s : G) : V ≃ᵢ V))⁻¹ := by
    intro k
    rw [hcs k]
    simp [commutatorElement_def]
  have hlin : ∀ k : ℕ, isoLin ((c k : G) : V ≃ᵢ V) = 1 := by
    intro k
    induction k with
    | zero => simpa [hc0] using ht
    | succ k ih =>
      rw [hcoe k, isoLin_mul, isoLin_mul, isoLin_mul, isoLin_inv, isoLin_inv, ih]
      simp
  have htr : ∀ k : ℕ, isoTr ((c k : G) : V ≃ᵢ V) = (N ^ k) u := by
    intro k
    induction k with
    | zero => simp [hc0, hu]
    | succ k ih =>
      rw [hcoe k, isoTr_comm_translation (((c k : G) : V ≃ᵢ V)) (((s : G) : V ≃ᵢ V)) (hlin k), ih]
      have hstep : N ((N ^ k) u) = (N ^ (k + 1)) u := by
        rw [show N ^ (k + 1) = N * N ^ k from pow_succ' N k]
        rfl
      rw [← hstep, hN, sub_apply]
      rfl
  have hmem : ∀ k : ℕ, c k ∈ (⊤ : Subgroup G).lowerCentralSeries k := by
    intro k
    induction k with
    | zero =>
      rw [Subgroup.lowerCentralSeries_zero]
      exact Subgroup.mem_top _
    | succ k ih =>
      rw [hcs k, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mem_commutator ih (Subgroup.mem_top s)
  have hlast : c n = 1 := by
    have hmem_n : c n ∈ (⊥ : Subgroup G) := by rw [← hn]; exact hmem n
    simpa using hmem_n
  have hu0 : (N ^ n) u = 0 := by
    have h1 := htr n
    rw [hlast] at h1
    simpa [isoTr_one] using h1.symm
  have hNu : N u = 0 := by
    have h := lin_sub_pow_eq_zero (isoLin ((s : G) : V ≃ᵢ V)) n u ?_
    · simpa [hN, hA] using h
    · simpa [hN, hA] using hu0
  have hc1 : ((c 1 : G) : V ≃ᵢ V) = 1 := by
    refine iso_eq_one_of _ (hlin 1) ?_
    rw [htr 1]
    simpa [pow_one] using hNu
  have hc1' : c 1 = 1 := Subtype.ext hc1
  have hc1eq : c 1 = ⁅t, s⁆ := by
    have h := hcs 0
    simp only [zero_add] at h
    rw [h, hc0]
  have hcomm : ⁅t, s⁆ = 1 := by rw [← hc1eq]; exact hc1'
  exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm

/-- conjugation of a translation by an isometry multiplies the vector by the linear part -/
lemma isoTr_conj (f t : V ≃ᵢ V) (ht : isoLin t = 1) :
    isoTr (f * t * f⁻¹) = isoLin f (isoTr t) := by
  rw [isoTr_mul, isoTr_mul, isoLin_mul, ht, mul_one, isoTr_inv]
  rw [map_neg, show isoLin f ((isoLin f)⁻¹ (isoTr f)) = isoTr f from by simp]
  abel

/-- inner product with a vector of the form `A v - v`, when `w` is fixed by `A` -/
lemma inner_eq_zero_of_fix (A : V ≃ₗᵢ[ℝ] V) (w v : V) (hw : A w = w) :
    inner ℝ w (A v - v) = 0 := by
  have h2 : A.symm w = w := by
    have h := congrArg A.symm hw
    rw [LinearIsometryEquiv.symm_apply_apply] at h
    exact h.symm
  have h1 : inner ℝ w (A v) = inner ℝ w v := by
    have h3 := LinearIsometryEquiv.inner_map_map A (A⁻¹ w) v
    rw [show A (A⁻¹ w) = w from LinearIsometryEquiv.apply_symm_apply A w,
      show A⁻¹ w = w from h2] at h3
    exact h3
  rw [inner_sub_right, h1, sub_self]

/-- A finite-index subgroup with commuting linear parts is abelian. -/
lemma comm_of_commuting_isoLin (G : Subgroup (V ≃ᵢ V)) (hnil : Group.IsNilpotent G)
    (G₁ : Subgroup G)
    (h : ∀ a : G₁, ∀ b : G₁, isoLin ((a : G) : V ≃ᵢ V) * isoLin ((b : G) : V ≃ᵢ V)
        = isoLin ((b : G) : V ≃ᵢ V) * isoLin ((a : G) : V ≃ᵢ V)) :
    ∀ a : G₁, ∀ b : G₁, (a : G) * (b : G) = (b : G) * (a : G) := by
  intro a b
  have hcoe : (((⁅a, b⁆ : G₁) : G) : V ≃ᵢ V)
      = ((a : G) : V ≃ᵢ V) * ((b : G) : V ≃ᵢ V) * (((a : G) : V ≃ᵢ V))⁻¹
        * (((b : G) : V ≃ᵢ V))⁻¹ := by
    simp [commutatorElement_def]
  have hlin : isoLin ((((⁅a, b⁆ : G₁) : G)) : V ≃ᵢ V) = 1 := by
    rw [hcoe, isoLin_mul, isoLin_mul, isoLin_mul, isoLin_inv, isoLin_inv, h a b]
    group
  have hmem : ((⁅a, b⁆ : G₁) : G) ∈ Subgroup.center G :=
    isoLin_eq_one_mem_center G hnil _ hlin
  set w : V := isoTr (((⁅a, b⁆ : G₁) : G) : V ≃ᵢ V) with hw
  have key : ∀ g : G, isoLin ((g : G) : V ≃ᵢ V) w = w := by
    intro g
    have h3 : g * ((⁅a, b⁆ : G₁) : G) * g⁻¹ = ((⁅a, b⁆ : G₁) : G) := by
      rw [(Subgroup.mem_center_iff.mp hmem) g, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : ((g : G) : V ≃ᵢ V) * ((((⁅a, b⁆ : G₁) : G)) : V ≃ᵢ V) * (((g : G) : V ≃ᵢ V))⁻¹
        = ((((⁅a, b⁆ : G₁) : G)) : V ≃ᵢ V) := by
      calc ((g : G) : V ≃ᵢ V) * ((((⁅a, b⁆ : G₁) : G)) : V ≃ᵢ V) * (((g : G) : V ≃ᵢ V))⁻¹
          = (((g * ((⁅a, b⁆ : G₁) : G) * g⁻¹ : G)) : V ≃ᵢ V) := by
            simp [Subgroup.coe_mul, Subgroup.coe_inv]
        _ = ((((⁅a, b⁆ : G₁) : G)) : V ≃ᵢ V) := by rw [h3]
    have h4 := isoTr_conj (((g : G) : V ≃ᵢ V)) ((((⁅a, b⁆ : G₁) : G)) : V ≃ᵢ V) hlin
    rw [h2, ← hw] at h4
    exact h4.symm
  have hform : w = (isoLin ((a : G) : V ≃ᵢ V) (isoTr ((b : G) : V ≃ᵢ V))
        - isoTr ((b : G) : V ≃ᵢ V))
      - (isoLin ((b : G) : V ≃ᵢ V) (isoTr ((a : G) : V ≃ᵢ V)) - isoTr ((a : G) : V ≃ᵢ V)) := by
    have hcomm := isoTr_comm_commuting (((a : G) : V ≃ᵢ V)) (((b : G) : V ≃ᵢ V)) (h a b)
    rw [← hcoe] at hcomm
    rw [hw]
    exact hcomm
  have hzerow : w = 0 := by
    have hX : inner ℝ w (isoLin ((a : G) : V ≃ᵢ V) (isoTr ((b : G) : V ≃ᵢ V))
        - isoTr ((b : G) : V ≃ᵢ V)) = 0 :=
      inner_eq_zero_of_fix (isoLin ((a : G) : V ≃ᵢ V)) w (isoTr ((b : G) : V ≃ᵢ V)) (key a)
    have hY : inner ℝ w (isoLin ((b : G) : V ≃ᵢ V) (isoTr ((a : G) : V ≃ᵢ V))
        - isoTr ((a : G) : V ≃ᵢ V)) = 0 :=
      inner_eq_zero_of_fix (isoLin ((b : G) : V ≃ᵢ V)) w (isoTr ((a : G) : V ≃ᵢ V)) (key b)
    have hinner : inner ℝ w w = 0 := by
      nth_rewrite 2 [hform]
      rw [inner_sub_right, hX, hY, sub_zero]
    exact inner_self_eq_zero.mp hinner
  have hone : ((((⁅a, b⁆ : G₁) : G)) : V ≃ᵢ V) = 1 :=
    iso_eq_one_of _ hlin (by rw [← hw]; exact hzerow)
  have hone' : ((⁅a, b⁆ : G₁) : G) = 1 := Subtype.ext hone
  have : ⁅(a : G), (b : G)⁆ = 1 := by
    have hcoe2 : ((⁅a, b⁆ : G₁) : G) = ⁅(a : G), (b : G)⁆ := by simp [commutatorElement_def]
    rw [← hcoe2]; exact hone'
  exact commutatorElement_eq_one_iff_mul_comm.mp this


/-- The linear-part map on the whole isometry group, as a monoid homomorphism. -/
def linPartHom : (V ≃ᵢ V) →* (V ≃ₗᵢ[ℝ] V) where
  toFun := isoLin
  map_one' := isoLin_one
  map_mul' := isoLin_mul


/-- **Nilpotent groups of Euclidean isometries are virtually abelian.** -/
theorem nilpotent_isometry_virtually_abelian {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (G : Subgroup (V ≃ᵢ V))
    (hpd : ∀ K : Set V, IsCompact K → {g : G | ((g : V ≃ᵢ V) '' K ∩ K).Nonempty}.Finite)
    (hnil : Group.IsNilpotent G) (hfg : G.FG) :
    ∃ A : Subgroup G, A.FiniteIndex ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  let Φ : (V ≃ᵢ V) →* (V ≃ₗᵢ[ℝ] V) := linPartHom
  let φ : G →* (V ≃ₗᵢ[ℝ] V) := Φ.comp G.subtype
  have hφ : ∀ x : G, φ x = isoLin ((x : G) : V ≃ᵢ V) := fun x => rfl
  -- the image of `G` under the linear-part map
  have hmem : ∀ x : G, φ x ∈ G.map Φ := fun x => ⟨(x : G), x.2, rfl⟩
  let ψ : G →* ↥(G.map Φ) := φ.codRestrict (G.map Φ) hmem
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hg, hgy⟩ := y.2
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    show ((ψ ⟨g, hg⟩ : ↥(G.map Φ)) : V ≃ₗᵢ[ℝ] V) = (y : V ≃ₗᵢ[ℝ] V)
    rw [show ((ψ ⟨g, hg⟩ : ↥(G.map Φ)) : V ≃ₗᵢ[ℝ] V) = φ ⟨g, hg⟩ from rfl, hφ]
    exact hgy
  have hPnil : Group.IsNilpotent ↥(G.map Φ) := by
    obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
    refine Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n, ?_⟩
    have h2 : Subgroup.map ψ ((⊤ : Subgroup G).lowerCentralSeries n)
        = (⊤ : Subgroup ↥(G.map Φ)).lowerCentralSeries n := by
      rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top, MonoidHom.range_eq_top.mpr hψ]
    rw [← h2, hn, Subgroup.map_bot]
  have hPfg : (G.map Φ).FG := by
    obtain ⟨S, hS, hSfin⟩ := (Subgroup.fg_iff G).mp hfg
    refine (Subgroup.fg_iff (G.map Φ)).mpr ⟨Φ '' S, ?_, hSfin.image Φ⟩
    rw [← hS, MonoidHom.map_closure]
  obtain ⟨P₁, hP₁, hP₁ab⟩ :=
    fg_nilpotent_orthogonal_virtually_abelian (G.map Φ) hPnil hPfg
  refine ⟨P₁.comap ψ, ?_, ?_⟩
  · rw [Subgroup.finiteIndex_iff] at hP₁ ⊢
    rw [Subgroup.index_comap_of_surjective P₁ hψ]
    exact hP₁
  · intro a ha b hb
    have hψcoe : ∀ x : G, ((ψ x : ↥(G.map Φ)) : V ≃ₗᵢ[ℝ] V) = isoLin ((x : G) : V ≃ᵢ V) := by
      intro x
      rw [show ((ψ x : ↥(G.map Φ)) : V ≃ₗᵢ[ℝ] V) = φ x from rfl, hφ]
    have hlin : ∀ x : P₁.comap ψ, ∀ y : P₁.comap ψ,
        isoLin (((x : G)) : V ≃ᵢ V) * isoLin (((y : G)) : V ≃ᵢ V)
          = isoLin (((y : G)) : V ≃ᵢ V) * isoLin (((x : G)) : V ≃ᵢ V) := by
      intro x y
      have h2 := congrArg (fun z : ↥(G.map Φ) => (z : V ≃ₗᵢ[ℝ] V)) (hP₁ab (ψ x) x.2 (ψ y) y.2)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hψcoe x, hψcoe y] at h2
      exact h2
    have h1 := comm_of_commuting_isoLin G hnil (P₁.comap ψ) hlin ⟨a, ha⟩ ⟨b, hb⟩
    simpa using h1

end

end Work.Mostow.Margulis

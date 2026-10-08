import Mathlib
import Submission.Work.PSU3.FineCoords.Setup
import Submission.Work.PSU3.FineCoords.psi_eq_norm
import Submission.Work.PSU3.FineCoords.quadratic_ext_iso
import Submission.Work.PSU3.FineCoords.norm_surjective
import Submission.Work.PSU3.FMap.mem_center_iff
import Submission.Work.PSU3.GaloisField.card_SZ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open scoped commutatorElement

open Work.ThmF

namespace Work.PSU3.CoarseFrame

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `SZ E` is finite when `E` is. -/
instance finiteSZ (E : Type*) [Field E] [FrobeniusInvolution E] [Finite E] : Finite (SZ E) :=
  Finite.of_injective (fun p : SZ E => (p.x, p.y)) (fun a b h => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact SZ.ext h1 h2)

/-! ## `ψ 1 ≠ 0` -/

lemma psi_one_ne_zero (fr : CoarseFrame H Q t n) : fr.psi 1 ≠ 0 := by
  intro h
  have h1 : ((fr.sect 1 : Q) : G) ^ 2 = 1 := by
    rw [← fr.zc_psi_val 1, h]
    show fr.zc (0 : E n) = 1
    exact fr.zc_zero
  have h2 : ((fr.sect 1 : Q) : G) ∈ fr.Q0 :=
    (fr.mem_Q0_iff _ (fr.sect 1).2).mpr h1
  have h3 : fr.barA (fr.sect 1) = 0 := (fr.barA_eq_zero_iff _).mpr h2
  rw [fr.sect_barA] at h3
  exact one_ne_zero h3

/-! ## The quotient map of `SZ (E n)` with the `μ`-twist -/

/-- The quotient map `p ↦ μ⁻¹ p.x` of `SZ (E n)` onto `E n`. -/
noncomputable def piMu (fr : CoarseFrame H Q t n) (μ : (E n)ˣ) :
    SZ (E n) →* Multiplicative (E n) where
  toFun p := Multiplicative.ofAdd ((μ : E n)⁻¹ * p.x)
  map_one' := by simp
  map_mul' := by
    intro p q
    simp only [SZ.mul_x, mul_add]
    rfl

lemma piMu_ker (fr : CoarseFrame H Q t n) (μ : (E n)ˣ) : (fr.piMu μ).ker = SZ.Q0 := by
  ext p
  rw [MonoidHom.mem_ker, SZ.mem_Q0_iff]
  constructor
  · intro h
    have h' : (μ : E n)⁻¹ * p.x = 0 := congrArg Multiplicative.toAdd h
    rcases mul_eq_zero.mp h' with h2 | h2
    · exact absurd h2 (by simpa using (Units.ne_zero μ⁻¹))
    · exact h2
  · intro h
    show Multiplicative.ofAdd ((μ : E n)⁻¹ * p.x) = 1
    rw [h, mul_zero]
    rfl

/-! ## Elementary facts about the two centres -/

lemma sq_mem_ker (fr : CoarseFrame H Q t n) (x : Q) : x ^ 2 ∈ fr.bar.ker := by
  rw [MonoidHom.mem_ker, map_pow, pow_two]
  rw [← Multiplicative.toAdd.injective.eq_iff]
  show fr.barA x + fr.barA x = 0
  exact CharTwo.add_self_eq_zero _

lemma sq_eq_one_of_mem_ker (fr : CoarseFrame H Q t n) {z : Q} (hz : z ∈ fr.bar.ker) :
    z * z = 1 := by
  have h0 : fr.barA z = 0 := by rw [barA, MonoidHom.mem_ker.mp hz]; rfl
  have hmem : (z : G) ∈ fr.Q0 := (fr.barA_eq_zero_iff z).mp h0
  apply Subtype.ext
  show (z : G) * (z : G) = 1
  simpa [pow_two] using fr.Q0_sq_eq_one ⟨_, hmem⟩

lemma ker_le_center (fr : CoarseFrame H Q t n) : fr.bar.ker ≤ Subgroup.center Q := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro y
  have h0 : fr.barA z = 0 := by rw [barA, MonoidHom.mem_ker.mp hz]; rfl
  have hmem : (z : G) ∈ fr.Q0 := (fr.barA_eq_zero_iff z).mp h0
  apply Subtype.ext
  show (y : G) * (z : G) = (z : G) * (y : G)
  exact (fr.Q0_central _ hmem y y.2).symm

lemma sz_sq_mem_Q0 (fr : CoarseFrame H Q t n) (x : SZ (E n)) : x ^ 2 ∈ SZ.Q0 := by
  rw [SZ.mem_Q0_iff, pow_two, SZ.mul_x]
  exact CharTwo.add_self_eq_zero _

lemma szQ0_sq_eq_one (fr : CoarseFrame H Q t n) {z : SZ (E n)} (hz : z ∈ SZ.Q0) :
    z * z = 1 := by
  have hx : z.x = 0 := hz
  apply SZ.ext
  · simp [hx]
  · simp only [SZ.mul_y, SZ.one_y, hx, map_zero, zero_mul, add_zero]
    exact CharTwo.add_self_eq_zero _

lemma szQ0_le_center (fr : CoarseFrame H Q t n) : SZ.Q0 ≤ Subgroup.center (SZ (E n)) := by
  have hσ : ∃ x : E n, σE x ≠ x := ⟨fr.uK, fr.uK_not_fixed⟩
  have hTr : ∀ c : E n, σE c = c → ∃ y : E n, y + σE y = c :=
    Work.PSU3.GaloisField.trace_surjective_of_exists_ne_fixed _ hσ
  intro z hz
  rw [Work.PSU3.mem_center_iff hσ hTr z]
  exact hz

/-! ## The identification `ker bar ≃* SZ.Q0` of the two centres -/

/-- `barA` vanishes on the kernel of `bar`. -/
lemma barA_of_mem_ker (fr : CoarseFrame H Q t n) {z : Q} (hz : z ∈ fr.bar.ker) :
    fr.barA z = 0 := by
  rw [barA, MonoidHom.mem_ker.mp hz]; rfl

/-- The `F`-coordinate of an element of `ker bar`. -/
noncomputable def kerCoordKer (fr : CoarseFrame H Q t n) (z : fr.bar.ker) : Fx n :=
  fr.zcEquiv.symm ⟨z.val, (fr.barA_eq_zero_iff z.val).mp (fr.barA_of_mem_ker z.property)⟩

/-- `zcEquiv` is additive (from `F` to `Q₀`). -/
lemma zcEquiv_add (fr : CoarseFrame H Q t n) (y y' : Fx n) :
    fr.zcEquiv (y + y') = fr.zcEquiv y * fr.zcEquiv y' := fr.zc0_add y y'

lemma kerCoordKer_mul (fr : CoarseFrame H Q t n) (z z' : fr.bar.ker) :
    fr.kerCoordKer (z * z') = fr.kerCoordKer z + fr.kerCoordKer z' := by
  apply fr.zcEquiv.injective
  simp only [kerCoordKer, Equiv.apply_symm_apply, fr.zcEquiv_add]
  exact Subtype.ext rfl

lemma kerCoordKer_one (fr : CoarseFrame H Q t n) : fr.kerCoordKer (1 : fr.bar.ker) = 0 := by
  apply fr.zcEquiv.injective
  simp only [kerCoordKer, Equiv.apply_symm_apply]
  rw [fr.zcEquiv_apply, fr.zc0_zero]
  simp

/-- The element of `SZ.Q0` attached to an element of `ker bar`. -/
noncomputable def gFun (fr : CoarseFrame H Q t n) (z : fr.bar.ker) : SZ.Q0 (E := E n) :=
  ⟨⟨0, (fr.kerCoordKer z : E n), by
      have h := (fr.kerCoordKer z).2
      rw [zero_mul, CharTwo.add_eq_zero]
      exact h.symm⟩, by rw [SZ.mem_Q0_iff]⟩

lemma gFun_mul_coe (fr : CoarseFrame H Q t n) (z z' : fr.bar.ker) :
    ((fr.gFun (z * z') : SZ.Q0 (E := E n)) : SZ (E n))
      = ((fr.gFun z : SZ.Q0 (E := E n)) : SZ (E n))
        * ((fr.gFun z' : SZ.Q0 (E := E n)) : SZ (E n)) := by
  apply SZ.ext
  · simp [gFun, SZ.mul_x]
  · simp only [gFun, SZ.mul_y, SZ.mul_x, zero_mul, add_zero]
    exact congrArg Subtype.val (fr.kerCoordKer_mul z z')

lemma gFun_mul (fr : CoarseFrame H Q t n) (z z' : fr.bar.ker) :
    fr.gFun (z * z') = fr.gFun z * fr.gFun z' :=
  Subtype.ext (fr.gFun_mul_coe z z')

lemma gFun_one_coe (fr : CoarseFrame H Q t n) :
    ((fr.gFun (1 : fr.bar.ker) : SZ.Q0 (E := E n)) : SZ (E n)) = 1 := by
  apply SZ.ext
  · simp [gFun]
  · simp only [gFun, SZ.one_y]
    rw [fr.kerCoordKer_one]
    rfl

lemma gFun_one (fr : CoarseFrame H Q t n) : fr.gFun (1 : fr.bar.ker) = 1 :=
  Subtype.ext (fr.gFun_one_coe)

lemma kerCoordKer_injective (fr : CoarseFrame H Q t n) : Function.Injective fr.kerCoordKer := by
  intro z z' h
  have h4 : (⟨z.1, (fr.barA_eq_zero_iff z.1).mp (fr.barA_of_mem_ker z.2)⟩ : fr.Q0)
      = ⟨z'.1, (fr.barA_eq_zero_iff z'.1).mp (fr.barA_of_mem_ker z'.2)⟩ := by
    have h5 := congrArg fr.zcEquiv h
    simpa only [kerCoordKer, Equiv.apply_symm_apply] using h5
  have h6 : (z.1 : G) = (z'.1 : G) := congrArg (Subtype.val : fr.Q0 → G) h4
  exact Subtype.ext (Subtype.ext h6)

lemma gFun_injective (fr : CoarseFrame H Q t n) : Function.Injective fr.gFun := by
  intro z z' h
  apply fr.kerCoordKer_injective
  have hh := congrArg (fun p : SZ.Q0 (E := E n) => p.val.y) h
  simpa [gFun] using hh

lemma gFun_surjective (fr : CoarseFrame H Q t n) : Function.Surjective fr.gFun := by
  intro p
  have hp : p.val.x = 0 := p.property
  have hy : σE p.val.y = p.val.y := by
    have h := p.val.herm
    rw [hp, map_zero, zero_mul, CharTwo.add_eq_zero] at h
    exact h.symm
  have hker : fr.Q0toQ ⟨fr.zc p.val.y, fr.zc_mem _ hy⟩ ∈ fr.bar.ker :=
    (fr.bar_eq_one_iff _).mpr (fr.zc_mem _ hy)
  refine ⟨⟨fr.Q0toQ ⟨fr.zc p.val.y, fr.zc_mem _ hy⟩, hker⟩, ?_⟩
  apply Subtype.ext
  apply SZ.ext
  · simp [gFun, hp]
  · simp only [gFun, SZ.mul_y, SZ.mul_x, zero_mul, add_zero]
    rw [show fr.kerCoordKer ⟨fr.Q0toQ ⟨fr.zc p.val.y, fr.zc_mem _ hy⟩, hker⟩
        = ⟨p.val.y, hy⟩ from by
      apply fr.zcEquiv.injective
      simp only [kerCoordKer, Equiv.apply_symm_apply]
      exact Subtype.ext rfl]

/-- The identification `ker bar ≃* SZ.Q0` of the two centres. -/
noncomputable def gKer (fr : CoarseFrame H Q t n) : fr.bar.ker ≃* SZ.Q0 (E := E n) :=
  MulEquiv.ofBijective
    ({ toFun := fr.gFun
       map_one' := fr.gFun_one
       map_mul' := fr.gFun_mul } : fr.bar.ker →* SZ.Q0 (E := E n))
    ⟨fr.gFun_injective, fr.gFun_surjective⟩

@[simp] lemma gKer_apply (fr : CoarseFrame H Q t n) (z : fr.bar.ker) :
    fr.gKer z = fr.gFun z := rfl

/-! ## Applying the classification of extensions -/

/-- The distinguished involution of `E n` is not the identity. -/
lemma exists_ne_fixed (fr : CoarseFrame H Q t n) : ∃ x : E n, σE x ≠ x :=
  ⟨fr.uK, fr.uK_not_fixed⟩

lemma trace_surj (fr : CoarseFrame H Q t n) :
    ∀ c : E n, σE c = c → ∃ y : E n, y + σE y = c :=
  Work.PSU3.GaloisField.trace_surjective_of_exists_ne_fixed _ fr.exists_ne_fixed

/-- A section of `SZ (E n) → E n`. -/
noncomputable def szSect (fr : CoarseFrame H Q t n) (b : E n) : SZ (E n) :=
  ⟨b, Classical.choose (fr.trace_surj (b * σE b) (by rw [map_mul, σE_σE, mul_comm])),
    (Classical.choose_spec (fr.trace_surj (b * σE b) (by rw [map_mul, σE_σE, mul_comm])))⟩

@[simp] lemma szSect_x (fr : CoarseFrame H Q t n) (b : E n) : (fr.szSect b).x = b := rfl

lemma piMu_surjective (fr : CoarseFrame H Q t n) (μ : (E n)ˣ) :
    Function.Surjective (fr.piMu μ) := by
  intro a
  refine ⟨fr.szSect ((μ : E n) * Multiplicative.toAdd a), ?_⟩
  show Multiplicative.ofAdd ((μ : E n)⁻¹ * ((μ : E n) * Multiplicative.toAdd a))
    = a
  rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero μ), one_mul]
  rfl

lemma kerCoordKer_sq (fr : CoarseFrame H Q t n) (x : Q) :
    fr.kerCoordKer ⟨x ^ 2, fr.sq_mem_ker x⟩ = fr.psi (fr.barA x) := by
  apply fr.zcEquiv.injective
  simp only [kerCoordKer, Equiv.apply_symm_apply]
  rw [show fr.zcEquiv (fr.psi (fr.barA x)) = fr.sqm (fr.barA x) from fr.zc0_psi (fr.barA x)]
  apply Subtype.ext
  exact fr.sq_eq_of_barA_eq (fr.sect_barA (fr.barA x)).symm

lemma sz_sq_y (y : SZ (E n)) : (y ^ 2).y = y.x * σE y.x := by
  rw [pow_two]
  simp only [SZ.mul_y]
  rw [CharTwo.add_self_eq_zero, zero_add]

lemma sz_sq_x (y : SZ (E n)) : (y ^ 2).x = 0 := by
  rw [pow_two, SZ.mul_x]
  exact CharTwo.add_self_eq_zero _

/-- The compatibility hypothesis of the classification of extensions. -/
lemma good_compat (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (μ : (E n)ˣ) (hμ : (μ : E n) * σE (μ : E n) = (fr.psi 1 : E n))
    (x : Q) (y : SZ (E n)) (hy : fr.piMu μ y = fr.bar x) :
    fr.gKer ⟨x ^ 2, fr.sq_mem_ker x⟩ = ⟨y ^ 2, fr.sz_sq_mem_Q0 y⟩ := by
  have hyx : y.x = (μ : E n) * fr.barA x := by
    have h' : (μ : E n)⁻¹ * y.x = fr.barA x := by
      have h := congrArg Multiplicative.toAdd hy
      simpa [piMu, barA] using h
    rw [← h', ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero μ), one_mul]
  have hRx : ((fr.gKer ⟨x ^ 2, fr.sq_mem_ker x⟩ : SZ.Q0 (E := E n)) : SZ (E n)).x = 0 := by
    rw [gKer_apply]
    simp only [gFun, SZ.mk_x]
  apply Subtype.ext
  apply SZ.ext
  · rw [show ((↑(⟨y ^ 2, fr.sz_sq_mem_Q0 y⟩ : SZ.Q0 (E := E n)) : SZ (E n)))
        = y ^ 2 from rfl, sz_sq_x, hRx]
  · rw [show ((↑(⟨y ^ 2, fr.sz_sq_mem_Q0 y⟩ : SZ.Q0 (E := E n)) : SZ (E n)))
        = y ^ 2 from rfl]
    simp only [gKer_apply, gFun]
    rw [fr.kerCoordKer_sq, sz_sq_y, hyx, map_mul]
    have e1 : (μ : E n) * fr.barA x * (σE (μ : E n) * σE (fr.barA x))
        = ((μ : E n) * σE (μ : E n)) * (fr.barA x * σE (fr.barA x)) := by ring
    rw [e1, hμ, ← psi_eq_mul_self fr hsq (fr.barA x)]

/-- A good isomorphism exists. -/
theorem exists_good (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2) :
    ∃ μ : (E n)ˣ, ∃ e₀ : Q ≃* SZ (E n), Good fr μ e₀ := by
  have hw0 : (fr.psi 1 : E n) ≠ 0 := fun h => fr.psi_one_ne_zero (Subtype.ext h)
  obtain ⟨μ, hμ⟩ := Work.PSU3.FineCoords.norm_surjective n (fr.psi 1 : E n) (fr.psi 1).2 hw0
  refine ⟨μ, ?_⟩
  obtain ⟨e, hx, hker⟩ := Work.PSU3.FineCoords.quadratic_ext_iso (A := E n) (P := Q)
    (P' := SZ (E n)) (Z := fr.bar.ker) (Z' := SZ.Q0 (E := E n))
    fr.ker_le_center (fun z hz => fr.sq_eq_one_of_mem_ker hz)
    fr.szQ0_le_center (fun z hz => fr.szQ0_sq_eq_one hz)
    fr.bar (fr.piMu μ) fr.bar_surjective (fr.piMu_surjective μ) rfl (fr.piMu_ker μ)
    fr.gKer fr.sq_mem_ker fr.sz_sq_mem_Q0 (fr.good_compat hsq μ hμ)
  refine ⟨e, ?_, ?_⟩
  · intro x
    have h := congrArg Multiplicative.toAdd (hx x)
    have h' : (μ : E n)⁻¹ * (e x).x = fr.barA x := by simpa [piMu, barA] using h
    show (e x).x = (μ : E n) * fr.barA x
    rw [← h', ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero μ), one_mul]
  · intro z hz
    have hmem : z ∈ fr.bar.ker := (fr.bar_eq_one_iff z).mpr ((fr.barA_eq_zero_iff z).mp hz)
    have h := hker ⟨z, hmem⟩
    exact h.trans rfl

end Work.PSU3.CoarseFrame

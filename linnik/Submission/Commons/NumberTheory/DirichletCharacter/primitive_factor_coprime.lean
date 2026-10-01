import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Factorisation of a primitive Dirichlet character over a coprime factorisation

If `χ` is a primitive Dirichlet character of modulus `u * v` with `u` and `v` coprime,
then `χ` is the product of a primitive character of modulus `u` and a primitive
character of modulus `v` (both lifted to modulus `u * v`).

The proof proceeds through the Chinese remainder theorem: the ring isomorphism
`ZMod (u*v) ≃+* ZMod u × ZMod v` identifies a unit of `ZMod (u*v)` with the pair
of its reductions modulo `u` and `v`, and hence the group `(ZMod (u*v))ˣ` with
`(ZMod u)ˣ × (ZMod v)ˣ`.  Restricting `χ` (viewed as a character of the unit group)
to the two factors gives characters of modulus `u` and `v`; the conductor
computation then shows that both are primitive.
-/

namespace Commons.NumberTheory.DirichletCharacter

variable {u v : ℕ} (huv : u.Coprime v)

/-- The Chinese remainder theorem ring isomorphism for the coprime moduli `u` and `v`. -/
noncomputable def crtE : ZMod (u * v) ≃+* ZMod u × ZMod v := ZMod.chineseRemainder huv

/-- The first component of `ZMod.chineseRemainder` is the reduction modulo `u`. -/
theorem crtE_fst (x : ZMod (u * v)) : (crtE huv x).1 = ZMod.cast x := by
  dsimp only [crtE]
  rw [show ZMod.chineseRemainder huv x =
      ZMod.castHom (show u.lcm v ∣ u*v by simp [Nat.lcm_dvd_iff]) (ZMod u × ZMod v) x from rfl]
  rw [ZMod.castHom_apply]
  exact Prod.fst_zmod_cast x

/-- The second component of `ZMod.chineseRemainder` is the reduction modulo `v`. -/
theorem crtE_snd (x : ZMod (u * v)) : (crtE huv x).2 = ZMod.cast x := by
  dsimp only [crtE]
  rw [show ZMod.chineseRemainder huv x =
      ZMod.castHom (show u.lcm v ∣ u*v by simp [Nat.lcm_dvd_iff]) (ZMod u × ZMod v) x from rfl]
  rw [ZMod.castHom_apply]
  exact Prod.snd_zmod_cast x

/-- The section of the reduction `(ZMod (u*v))ˣ → (ZMod u)ˣ` sending a unit to the unit
congruent to it modulo `u` and to `1` modulo `v`. -/
noncomputable def crtSu : (ZMod u)ˣ →* (ZMod (u*v))ˣ :=
  (Units.map (crtE huv).symm.toMonoidHom).comp (Units.map (MonoidHom.inl (ZMod u) (ZMod v)))

/-- The section of the reduction `(ZMod (u*v))ˣ → (ZMod v)ˣ` sending a unit to the unit
congruent to it modulo `v` and to `1` modulo `u`. -/
noncomputable def crtSv : (ZMod v)ˣ →* (ZMod (u*v))ˣ :=
  (Units.map (crtE huv).symm.toMonoidHom).comp (Units.map (MonoidHom.inr (ZMod u) (ZMod v)))

/-- `crtSu` is a section of the reduction modulo `u`. -/
theorem crtSu_unitsMap (a : (ZMod u)ˣ) :
    ZMod.unitsMap (Nat.dvd_mul_right u v) (crtSu huv a) = a := by
  apply Units.ext
  rw [ZMod.unitsMap_val]
  rw [show ((crtSu huv a : (ZMod (u*v))ˣ) : ZMod (u*v)) = (crtE huv).symm (a, 1) by
     simp [crtSu, MonoidHom.inl_apply]]
  rw [← crtE_fst huv ((crtE huv).symm (a,1))]
  rw [RingEquiv.apply_symm_apply]

/-- `crtSv` is a section of the reduction modulo `v`. -/
theorem crtSv_unitsMap (b : (ZMod v)ˣ) :
    ZMod.unitsMap (Nat.dvd_mul_left v u) (crtSv huv b) = b := by
  apply Units.ext
  rw [ZMod.unitsMap_val]
  rw [show ((crtSv huv b : (ZMod (u*v))ˣ) : ZMod (u*v)) = (crtE huv).symm (1, b) by
     simp [crtSv, MonoidHom.inr_apply]]
  rw [← crtE_snd huv ((crtE huv).symm (1,b))]
  rw [RingEquiv.apply_symm_apply]

/-- Every unit of `ZMod (u*v)` is the product of the two sections applied to its
reductions modulo `u` and modulo `v`. -/
theorem crtSu_mul_crtSv (x : (ZMod (u*v))ˣ) :
    crtSu huv (ZMod.unitsMap (Nat.dvd_mul_right u v) x) *
    crtSv huv (ZMod.unitsMap (Nat.dvd_mul_left v u) x) = x := by
  apply Units.ext
  refine (crtE huv).injective ?_
  rw [Units.val_mul, map_mul]
  rw [show ((crtSu huv (ZMod.unitsMap (Nat.dvd_mul_right u v) x) : (ZMod (u*v))ˣ) : ZMod (u*v))
        = (crtE huv).symm (ZMod.unitsMap (Nat.dvd_mul_right u v) x, 1) by
      simp [crtSu, MonoidHom.inl_apply]]
  rw [show ((crtSv huv (ZMod.unitsMap (Nat.dvd_mul_left v u) x) : (ZMod (u*v))ˣ) : ZMod (u*v))
        = (crtE huv).symm (1, ZMod.unitsMap (Nat.dvd_mul_left v u) x) by
      simp [crtSv, MonoidHom.inr_apply]]
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rw [Prod.mk_mul_mk, mul_one, one_mul]
  rw [show ((crtE huv) (↑x : ZMod (u*v))) =
      ((ZMod.unitsMap (Nat.dvd_mul_right u v) x : ZMod u),
       (ZMod.unitsMap (Nat.dvd_mul_left v u) x : ZMod v)) from by
    refine Prod.ext ?_ ?_
    · simp only [crtE_fst, ZMod.unitsMap_val]
    · simp only [crtE_snd, ZMod.unitsMap_val]]

/-- `toUnitHom` is a left inverse of `ofUnitHom`. -/
theorem ofUnitHom_toUnitHom {R R' : Type*} [CommMonoidWithZero R] [CommMonoidWithZero R']
    (f : Rˣ →* R'ˣ) : (MulChar.ofUnitHom f).toUnitHom = f := by
  rw [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]

/-- The `u`-component of a character of modulus `u*v`, as a multiplicativity-preserving
homomorphism of the unit group of `ZMod u`. -/
noncomputable def factorLeft (χ : DirichletCharacter ℂ (u*v)) : DirichletCharacter ℂ u :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (crtSu huv))

/-- The `v`-component of a character of modulus `u*v`, as a multiplicativity-preserving
homomorphism of the unit group of `ZMod v`. -/
noncomputable def factorRight (χ : DirichletCharacter ℂ (u*v)) : DirichletCharacter ℂ v :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (crtSv huv))

/-- A character of modulus `u * v` is the product of its two components (lifted to
modulus `u * v`). -/
theorem factor_eq (χ : DirichletCharacter ℂ (u*v)) :
    (factorLeft huv χ).changeLevel (Nat.dvd_mul_right u v) *
    (factorRight huv χ).changeLevel (Nat.dvd_mul_left v u) = χ := by
  refine (DirichletCharacter.toUnitHom_inj (χ := (factorLeft huv χ).changeLevel (Nat.dvd_mul_right u v) *
      (factorRight huv χ).changeLevel (Nat.dvd_mul_left v u)) χ).mp ?_
  refine MonoidHom.ext (fun x => ?_)
  rw [show (MulChar.toUnitHom ((factorLeft huv χ).changeLevel (Nat.dvd_mul_right u v) *
        (factorRight huv χ).changeLevel (Nat.dvd_mul_left v u))) x
      = (MulChar.toUnitHom ((factorLeft huv χ).changeLevel (Nat.dvd_mul_right u v))) x *
        (MulChar.toUnitHom ((factorRight huv χ).changeLevel (Nat.dvd_mul_left v u))) x from
      MulChar.equivToUnitHom_mul_apply _ _ x]
  rw [DirichletCharacter.changeLevel_toUnitHom, DirichletCharacter.changeLevel_toUnitHom]
  simp only [MonoidHom.comp_apply, ofUnitHom_toUnitHom, factorLeft, factorRight]
  rw [← map_mul, crtSu_mul_crtSv]

variable {u v : ℕ} [NeZero u] [NeZero v] (huv : u.Coprime v)

/-- The `u`-component of a primitive character of modulus `u * v` (with `u`, `v` coprime)
is primitive of modulus `u`. -/
theorem factorLeft_isPrimitive (χ : DirichletCharacter ℂ (u*v)) (hχ : χ.IsPrimitive) :
    (factorLeft huv χ).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hcon : χ.conductor = u * v := hχ
  have ha : (factorLeft huv χ).conductor ∣ u := DirichletCharacter.conductor_dvd_level _
  have hb : (factorRight huv χ).conductor ∣ v := DirichletCharacter.conductor_dvd_level _
  have hAc : ((factorLeft huv χ).changeLevel (Nat.dvd_mul_right u v)).conductor =
      (factorLeft huv χ).conductor :=
    DirichletCharacter.conductor_changeLevel _ (Nat.dvd_mul_right u v)
  have hBc : ((factorRight huv χ).changeLevel (Nat.dvd_mul_left v u)).conductor =
      (factorRight huv χ).conductor :=
    DirichletCharacter.conductor_changeLevel _ (Nat.dvd_mul_left v u)
  have hdvd : u * v ∣ (factorLeft huv χ).conductor.lcm (factorRight huv χ).conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor
      ((factorLeft huv χ).changeLevel (Nat.dvd_mul_right u v))
      ((factorRight huv χ).changeLevel (Nat.dvd_mul_left v u))
    rw [factor_eq huv χ, hAc, hBc] at h
    rwa [hcon] at h
  have hlcm : (factorLeft huv χ).conductor.lcm (factorRight huv χ).conductor = u * v := by
    refine le_antisymm ?_ ?_
    · exact Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne u))
        (Nat.pos_of_ne_zero (NeZero.ne v)))
        (Nat.lcm_dvd (Nat.dvd_trans ha (Nat.dvd_mul_right u v))
                     (Nat.dvd_trans hb (Nat.dvd_mul_left v u)))
    · exact Nat.le_of_dvd (Nat.lcm_pos (Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _))
        (Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _))) hdvd
  have hcop : (factorLeft huv χ).conductor.Coprime (factorRight huv χ).conductor :=
    Nat.Coprime.of_dvd ha hb huv
  have hmul : (factorLeft huv χ).conductor * (factorRight huv χ).conductor = u * v := by
    rw [← hcop.lcm_eq_mul, hlcm]
  have hleu : (factorLeft huv χ).conductor ≤ u :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne u)) ha
  rcases lt_or_eq_of_le hleu with hlt | heq
  · exfalso
    have hbpos : 0 < (factorRight huv χ).conductor :=
      Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _)
    have hbv : (factorRight huv χ).conductor ≤ v :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne v)) hb
    have h1 : (factorLeft huv χ).conductor * (factorRight huv χ).conductor <
              u * (factorRight huv χ).conductor := Nat.mul_lt_mul_of_pos_right hlt hbpos
    have h2 : u * (factorRight huv χ).conductor ≤ u * v := Nat.mul_le_mul_left u hbv
    omega
  · exact heq

/-- The `v`-component of a primitive character of modulus `u * v` (with `u`, `v` coprime)
is primitive of modulus `v`. -/
theorem factorRight_isPrimitive (χ : DirichletCharacter ℂ (u*v)) (hχ : χ.IsPrimitive) :
    (factorRight huv χ).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hcon : χ.conductor = u * v := hχ
  have ha : (factorLeft huv χ).conductor ∣ u := DirichletCharacter.conductor_dvd_level _
  have hb : (factorRight huv χ).conductor ∣ v := DirichletCharacter.conductor_dvd_level _
  have hAc : ((factorLeft huv χ).changeLevel (Nat.dvd_mul_right u v)).conductor =
      (factorLeft huv χ).conductor :=
    DirichletCharacter.conductor_changeLevel _ (Nat.dvd_mul_right u v)
  have hBc : ((factorRight huv χ).changeLevel (Nat.dvd_mul_left v u)).conductor =
      (factorRight huv χ).conductor :=
    DirichletCharacter.conductor_changeLevel _ (Nat.dvd_mul_left v u)
  have hdvd : u * v ∣ (factorLeft huv χ).conductor.lcm (factorRight huv χ).conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor
      ((factorLeft huv χ).changeLevel (Nat.dvd_mul_right u v))
      ((factorRight huv χ).changeLevel (Nat.dvd_mul_left v u))
    rw [factor_eq huv χ, hAc, hBc] at h
    rwa [hcon] at h
  have hlcm : (factorLeft huv χ).conductor.lcm (factorRight huv χ).conductor = u * v := by
    refine le_antisymm ?_ ?_
    · exact Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne u))
        (Nat.pos_of_ne_zero (NeZero.ne v)))
        (Nat.lcm_dvd (Nat.dvd_trans ha (Nat.dvd_mul_right u v))
                     (Nat.dvd_trans hb (Nat.dvd_mul_left v u)))
    · exact Nat.le_of_dvd (Nat.lcm_pos (Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _))
        (Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _))) hdvd
  have hcop : (factorLeft huv χ).conductor.Coprime (factorRight huv χ).conductor :=
    Nat.Coprime.of_dvd ha hb huv
  have hmul : (factorLeft huv χ).conductor * (factorRight huv χ).conductor = u * v := by
    rw [← hcop.lcm_eq_mul, hlcm]
  have hlev : (factorRight huv χ).conductor ≤ v :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne v)) hb
  rcases lt_or_eq_of_le hlev with hlt | heq
  · exfalso
    have hapos : 0 < (factorLeft huv χ).conductor :=
      Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _)
    have hau : (factorLeft huv χ).conductor ≤ u :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne u)) ha
    have h1 : (factorLeft huv χ).conductor * (factorRight huv χ).conductor <
              (factorLeft huv χ).conductor * v := Nat.mul_lt_mul_of_pos_left hlt hapos
    have h2 : (factorLeft huv χ).conductor * v ≤ u * v := Nat.mul_le_mul_right v hau
    omega
  · exact heq

/-- **Factorisation of a primitive Dirichlet character over coprime moduli.**
If `u` and `v` are coprime and `χ` is a primitive Dirichlet character of modulus `u * v`,
then `χ` is the product of a primitive character of modulus `u` and a primitive character of
modulus `v`, both lifted to modulus `u * v`. -/
theorem primitive_factor_coprime {u v : ℕ} [NeZero u] [NeZero v] (huv : u.Coprime v)
    (χ : DirichletCharacter ℂ (u * v)) (hχ : χ.IsPrimitive) :
    ∃ (χu : DirichletCharacter ℂ u) (χv : DirichletCharacter ℂ v),
      χu.IsPrimitive ∧ χv.IsPrimitive ∧
      χ = (χu.changeLevel (Nat.dvd_mul_right u v)) * (χv.changeLevel (Nat.dvd_mul_left v u)) := by
  exact ⟨factorLeft huv χ, factorRight huv χ, factorLeft_isPrimitive huv χ hχ,
    factorRight_isPrimitive huv χ hχ, (factor_eq huv χ).symm⟩

end Commons.NumberTheory.DirichletCharacter
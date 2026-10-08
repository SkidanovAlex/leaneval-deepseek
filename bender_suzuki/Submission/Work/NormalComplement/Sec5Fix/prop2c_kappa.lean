import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.NormalComplement.appIII
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.Sec5Fix.prop2c_local_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.Sec5Fix

variable {G : Type} [Group G]

/-! ## The `Mset`-calculus

`Design.Mset u t = {x | x ∈ C_G({u * t}) ∧ t * x * t⁻¹ = x⁻¹}` is the underlying set of the
abelian subgroup `M` of §5 Prop. 2 (b).  For the construction of `κ ⊆ Mset u t` normalised by
`N_G(P)` we only need the following elementary closure properties, which show that any subgroup
of `N_G(P)` all of whose elements commute with `u * t` and are inverted by `u` lies in
`Mset u t`. -/

/-- `Mset u t` is closed under inverses. -/
theorem mset_inv_mem {u t x : G} (hx : Work.NormalComplement.Design.Mset u t x) :
    Work.NormalComplement.Design.Mset u t x⁻¹ := by
  obtain ⟨hc, hi⟩ := hx
  have hc' : x * (u * t) = (u * t) * x := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h : x⁻¹ * (u * t) * x = u * t := by
      rw [mul_assoc, hc'.symm, inv_mul_cancel_left]
    calc x⁻¹ * (u * t) = x⁻¹ * (u * t) * x * x⁻¹ := by group
      _ = (u * t) * x⁻¹ := by rw [h]
  · calc t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      _ = x⁻¹⁻¹ := by rw [hi]

/-- `Mset u t` is closed under products of commuting elements: since `t` inverts both factors, the
only obstruction to multiplicativity is the commutativity of the factors. -/
theorem mset_mul_mem_of_commute {u t x y : G} (hx : Work.NormalComplement.Design.Mset u t x)
    (hy : Work.NormalComplement.Design.Mset u t y) (hxy : x * y = y * x) :
    Work.NormalComplement.Design.Mset u t (x * y) := by
  obtain ⟨hxc, hxi⟩ := hx
  obtain ⟨hyc, hyi⟩ := hy
  have hxc' : x * (u * t) = (u * t) * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
  have hyc' : y * (u * t) = (u * t) * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x * y) * (u * t) = x * (y * (u * t)) := by group
      _ = x * ((u * t) * y) := by rw [hyc']
      _ = (x * (u * t)) * y := by group
      _ = ((u * t) * x) * y := by rw [hxc']
      _ = (u * t) * (x * y) := by group
  · calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [hxi, hyi]
      _ = (x * y)⁻¹ := by
            rw [mul_inv_rev]
            have h := congrArg (fun z : G => z⁻¹) hxy
            simpa [mul_inv_rev] using h.symm

/-- `u * t ∈ Mset u t` when `u` and `t` are involutions: `u t` centralises itself and `t` inverts
it. -/
theorem mset_mem_mul_of_involutions {u t : G} (hu : orderOf u = 2) (ht : orderOf t = 2) :
    Work.NormalComplement.Design.Mset u t (u * t) := by
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu] at h
    simpa [pow_two] using h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have key : t * (u * t) * t⁻¹ = (u * t)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu2, inv_eq_of_mul_eq_one_right ht2]
    calc t * (u * t) * t = t * u * (t * t) := by group
      _ = t * u := by rw [ht2, mul_one]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl _), key⟩

/-- A subgroup `κ ≤ N_G(P)` all of whose elements are inverted by `u` and commute with `u * t`
lies in `Mset u t`: this is the verification used at the end of §5 Prop. 2 (c) for
`κ = O_f(Q) ⊆ J(Q,u)`. -/
theorem mset_of_le_of_inverted {u t : G} (hu : orderOf u = 2) (ht : orderOf t = 2)
    {κ : Subgroup G} (hut : u * t ∈ κ)
    (hinv : ∀ x ∈ κ, u * x * u⁻¹ = x⁻¹)
    (hcom : ∀ x ∈ κ, x * (u * t) = (u * t) * x) :
    (κ : Set G) ⊆ Work.NormalComplement.Design.Mset u t := by
  intro x hx
  have hxcomm : Commute x (u * t) := hcom x hx
  -- `t = u * (u * t)`, so `t` inverts `x` as soon as `u` does and `x` commutes with `u * t`.
  have htinv : t * x * t⁻¹ = x⁻¹ := by
    have h1 : t = u * (u * t) := by
      have hu2 : u * u = 1 := by
        have h := pow_orderOf_eq_one u
        rw [hu] at h
        simpa [pow_two] using h
      rw [← mul_assoc, hu2, one_mul]
    have h2 : u * ((u * t) * x * (u * t)⁻¹) * u⁻¹ = u * x * u⁻¹ := by
      rw [show (u * t) * x * (u * t)⁻¹ = x from by rw [← hxcomm]; group]
    rw [h1, show (u * (u * t)) * x * (u * (u * t))⁻¹ =
        u * ((u * t) * x * (u * t)⁻¹) * u⁻¹ from by group]
    rw [h2, hinv x hx]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxcomm, htinv⟩

/-- Conjugation commutes with powers: `(g x g⁻¹) ^ n = g x ^ n g⁻¹`. -/
theorem pow_conj_eq (g x : G) (n : ℕ) : (g * x * g⁻¹) ^ n = g * x ^ n * g⁻¹ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ih]; group

/-- **§5 Prop. 2 (c), the subgroup `κ`** (Peterfalvi I Ch. III, p. 185): there is a subgroup
`κ ⊆ Mset u t` containing `u * t` and normalised by `N_G(P)`.  It is obtained from
`Sec5Fix.prop2c_local_Q` (Appendix III on `N_G(P)/P`) as the `f`-part of the abelian group `Q`
produced there. -/
theorem prop2c_kappa (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    ∃ κ : Subgroup G, (κ : Set G) ⊆ Work.NormalComplement.Design.Mset u t ∧
      u * t ∈ κ ∧
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (κ : Set G) := by
  classical
  -- The local group theory of §5 Prop. 2 (c): `Sec5Fix.prop2c_local_Q` produces
  -- `f` prime, `f ≠ p`, and an *abelian* subgroup `Q ⊴ N_G(P)` with `P ≤ Q`, `u * t ∈ Q`,
  -- `x ^ f ∈ P` and `u * x * u⁻¹ * x ∈ P` for all `x ∈ Q` (Appendix III on `N_G(P)/P` applied
  -- to `Ω_P`, together with App. I (5) b).
  obtain ⟨f, Q, hfprime, hf_ne_p, hPQ, hQN, hutQ, hQab, hQexp, hinv⟩ :=
    prop2c_local_Q hFT hA hC hC4 hP3 hIII hMF2 hCor1 h u hu
  --   κ := {x ∈ Q | x ^ f = 1}  =  O_f(Q),
  --
  -- a subgroup because `Q` is abelian, and characteristic in `Q`, hence normalised by `N_G(P)`
  -- since `Q ⊴ N_G(P)`.
  let κ : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ x ^ f = 1}
      mul_mem' := by
        rintro x y ⟨hxQ, hx1⟩ ⟨hyQ, hy1⟩
        refine ⟨Q.mul_mem hxQ hyQ, ?_⟩
        rw [Commute.mul_pow (hQab x hxQ y hyQ) f, hx1, hy1, one_mul]
      one_mem' := ⟨Q.one_mem, one_pow f⟩
      inv_mem' := by
        rintro x ⟨hxQ, hx1⟩
        exact ⟨Q.inv_mem hxQ, by rw [inv_pow, hx1, inv_one]⟩ }
  have hmemκ : ∀ x : G, x ∈ κ ↔ x ∈ Q ∧ x ^ f = 1 := fun x => Iff.rfl
  -- ## `u` is an involution inverting `u * t`
  have hu2 : u * u = 1 := by
    have h' := pow_orderOf_eq_one u; rw [hu.2.1] at h'; simpa [pow_two] using h'
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have ht2 : t * t = 1 := by
    have h' := pow_orderOf_eq_one t; rw [h.invol] at h'; simpa [pow_two] using h'
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hutinv : u * (u * t) * u⁻¹ = (u * t)⁻¹ := by
    have h1 : u * (u * t) * u⁻¹ = t * u := by
      rw [hu_inv, show u * (u * t) * u = (u * u) * t * u from by group, hu2, one_mul]
    rw [h1, mul_inv_rev, ht_inv, hu_inv]
  -- ## `u * t ∈ κ`
  --
  -- * `u * t ∈ κ`: `(u * t) ^ f ∈ P` (as `u * t ∈ Q`), and `u` both inverts it (it inverts
  --   `u * t`, so it inverts its powers) and centralises it (`(u * t) ^ f ∈ P ≤ centD H t`,
  --   centralised by `u`); hence `((u * t) ^ f) ^ 2 = 1`, which forces `(u * t) ^ f = 1` in the
  --   odd-order group `P`.
  have hyP : (u * t) ^ f ∈ P := hQexp (u * t) hutQ
  have hu_y : u * ((u * t) ^ f) * u⁻¹ = (u * t) ^ f := by
    have hc := (Subgroup.mem_centralizer_iff.mp hu.2.2) ((u * t) ^ f) (h.P_le hyP).2
    rw [← hc]; group
  have hu_inv_y : u * ((u * t) ^ f) * u⁻¹ = ((u * t) ^ f)⁻¹ := by
    have h := pow_conj_eq u (u * t) f
    rw [hutinv, inv_pow] at h
    exact h.symm
  have hyy : (u * t) ^ f * (u * t) ^ f = 1 := by
    have hyeq : ((u * t) ^ f)⁻¹ = (u * t) ^ f := hu_inv_y.symm.trans hu_y
    exact mul_eq_one_iff_eq_inv.mpr hyeq.symm
  have hy1 : (u * t) ^ f = 1 := by
    have h1 : orderOf ((u * t) ^ f) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have h2 : orderOf ((u * t) ^ f) ∣ Nat.card ↥P := Subgroup.orderOf_dvd_natCard P hyP
    rw [h.P_card] at h2
    have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (h.prime.odd_of_ne_two (p_ne_two' h))
    have h3 : orderOf ((u * t) ^ f) ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 2 p = 1 from hcop] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hutκ : u * t ∈ κ := (hmemκ (u * t)).mpr ⟨hutQ, hy1⟩
  -- ## `u` inverts every element of `κ`
  --
  -- * `u * x * u⁻¹ = x⁻¹` for `x ∈ κ`: `z := u * x * u⁻¹ * x ∈ P` and
  --   `z ^ f = (u * x * u⁻¹) ^ f * x ^ f = u * x ^ f * u⁻¹ * x ^ f = 1`, so `orderOf z ∣ p` and
  --   `orderOf z ∣ f`, whence `z = 1` as `f ≠ p`; this is exactly `u * x * u⁻¹ = x⁻¹`.
  have hinvOnK : ∀ x ∈ κ, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨hxQ, hxf⟩ := (hmemκ x).mp hx
    have hzP : u * x * u⁻¹ * x ∈ P := hinv x hxQ
    have huxQ : u * x * u⁻¹ ∈ Q := by
      have h1 : u * x * u⁻¹ = (u * x * u⁻¹ * x) * x⁻¹ := by group
      rw [h1]
      exact Q.mul_mem (hPQ hzP) (Q.inv_mem hxQ)
    have hzf : (u * x * u⁻¹ * x) ^ f = 1 := by
      rw [Commute.mul_pow (hQab (u * x * u⁻¹) huxQ x hxQ) f, pow_conj_eq u x f, hxf]
      group
    have hz1 : u * x * u⁻¹ * x = 1 := by
      have h1 : orderOf (u * x * u⁻¹ * x) ∣ f := orderOf_dvd_iff_pow_eq_one.mpr hzf
      have h2 : orderOf (u * x * u⁻¹ * x) ∣ Nat.card ↥P :=
        Subgroup.orderOf_dvd_natCard P hzP
      rw [h.P_card] at h2
      have hcop : Nat.Coprime f p := (Nat.coprime_primes hfprime h.prime).mpr hf_ne_p
      have h3 : orderOf (u * x * u⁻¹ * x) ∣ 1 := by
        have := Nat.dvd_gcd h1 h2
        rwa [show Nat.gcd f p = 1 from hcop] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    exact mul_eq_one_iff_eq_inv.mp hz1
  -- * `x * (u * t) = (u * t) * x` for `x ∈ κ` since `Q` is abelian and contains `u * t`.
  have hcomOnK : ∀ x ∈ κ, x * (u * t) = (u * t) * x :=
    fun x hx => hQab x ((hmemκ x).mp hx).1 (u * t) hutQ
  -- * `κ ⊆ Mset u t` is then `mset_of_le_of_inverted` above.
  have hsub : (κ : Set G) ⊆ Work.NormalComplement.Design.Mset u t :=
    mset_of_le_of_inverted hu.2.1 h.invol hutκ hinvOnK hcomOnK
  -- ## `N_G(P)` normalises `κ`
  --
  -- `κ = O_f(Q)` is characteristic in `Q`, and `Q ⊴ N_G(P)`: for `g ∈ N_G(P)` and `x ∈ G` we
  -- have `g x g⁻¹ ∈ Q ↔ x ∈ Q` and `(g x g⁻¹) ^ f = g x ^ f g⁻¹`, so `g` preserves `κ`.
  have hconjκ : ∀ g : G, g ∈ Subgroup.normalizer (P : Set G) → ∀ x : G, x ∈ κ → g * x * g⁻¹ ∈ κ := by
    intro g hg x hx
    obtain ⟨hxQ, hxf⟩ := (hmemκ x).mp hx
    have hQmem := Subgroup.mem_set_normalizer_iff.mp (hQN hg)
    refine (hmemκ (g * x * g⁻¹)).mpr ⟨(hQmem x).mp hxQ, ?_⟩
    rw [pow_conj_eq g x f, hxf]; group
  refine ⟨κ, hsub, hutκ, ?_⟩
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  refine fun x => ⟨hconjκ g hg x, fun hx => ?_⟩
  have h2 := hconjκ g⁻¹ ((Subgroup.normalizer (P : Set G)).inv_mem hg) (g * x * g⁻¹) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x from by group] at h2

end Work.NormalComplement.Sec5Fix

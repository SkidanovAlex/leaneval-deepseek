import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.omega_isPGroup
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The central-product decomposition attached to a class-two `p`-group with cyclic centre

Let `X` be a finite `p`-group (`p` an odd prime) of nilpotency class at most two
(`⁅X, X⁆ ≤ Z(X)`) whose centre is cyclic, whose derived subgroup has order `p`, and such that
every `p`-th power of an element of `X` is again a `p`-th power of a central element.

Then `X` is the internal central product of a cyclic subgroup `Cc` (namely `Z(X)`) and an
extraspecial subgroup `E` of exponent `p` (namely `Ω₁(X)`, the subgroup of elements of order
dividing `p`).

The proof rests on three observations.

* The `p`-th power map is multiplicative on the set of elements of order dividing `p`: since
  `X` is of class two, `(xy)^p = x^p y^p ⁅y,x⁆^{p(p-1)/2}`, and `⁅y,x⁆^p = 1` while `p` is odd.
  Hence `Ω₁(X) = {x : x^p = 1}` is a subgroup (`pow_mul_eq_of_class_two`, `S`/`hEeqS`).
* `Z(X) · Ω₁(X) = X`: the hypothesis on `p`-th powers lets every element be written as an
  element of `Ω₁(X)` times a central element (`top_eq_center_sup`).
* Combined with the cyclic centre, `Z(X) ∩ Ω₁(X) = ⁅X, X⁆`, so the centre of `Ω₁(X)` is the
  order-`p` group `⁅X, X⁆` (`centerIn_eq_inf_center`, `inf_center_eq_commutator`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

/-! ### The power map in a class-two group whose commutators have exponent dividing `p` -/

/-- **Power formula in a group of nilpotency class at most two.**
If `⁅G, G⁆ ≤ Z(G)` then `(x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)` for all
`x y : G` and all `n`. -/
theorem pow_mul_eq_of_class_two_aux {G : Type*} [Group G]
    (hclass : (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G) ≤ Subgroup.center G) (x y : G) :
    ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2) := by
  have hc : ⁅y, x⁆ ∈ Subgroup.center G :=
    hclass (Subgroup.commutator_mem_commutator trivial trivial)
  have hcomm : Commute y ⁅y, x⁆ := Subgroup.mem_center_iff.mp hc y
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hcpow : ∀ m : ℕ, ⁅y, x⁆ ^ m ∈ Subgroup.center G :=
      fun m => (Subgroup.center G).pow_mem hc m
    have hpow : ⁅y ^ n, x⁆ = ⁅y, x⁆ ^ n := (hcomm.commutatorElement_pow_left n).symm
    have hcx : ⁅y, x⁆ ^ n * x = x * ⁅y, x⁆ ^ n :=
      (Subgroup.mem_center_iff.mp (hcpow n) x).symm
    have hcy : ⁅y, x⁆ ^ n * y ^ n = y ^ n * ⁅y, x⁆ ^ n :=
      (Subgroup.mem_center_iff.mp (hcpow n) (y ^ n)).symm
    have hkey : y ^ n * x = x * y ^ n * ⁅y, x⁆ ^ n := by
      have h1 : y ^ n * x = ⁅y ^ n, x⁆ * (x * y ^ n) := by
        rw [commutatorElement_def]; group
      rw [h1, hpow, ← mul_assoc, hcx, mul_assoc, hcy, ← mul_assoc]
    have hcyC : ⁅y, x⁆ ^ (n.choose 2) * (x * y) = (x * y) * ⁅y, x⁆ ^ (n.choose 2) :=
      (Subgroup.mem_center_iff.mp (hcpow (n.choose 2)) (x * y)).symm
    have hcpy : ⁅y, x⁆ ^ n * y = y * ⁅y, x⁆ ^ n :=
      (Subgroup.mem_center_iff.mp (hcpow n) y).symm
    rw [pow_succ, ih]
    calc x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2) * (x * y)
        = x ^ n * y ^ n * (⁅y, x⁆ ^ (n.choose 2) * (x * y)) := by group
      _ = x ^ n * y ^ n * ((x * y) * ⁅y, x⁆ ^ (n.choose 2)) := by rw [hcyC]
      _ = x ^ n * (y ^ n * x) * y * ⁅y, x⁆ ^ (n.choose 2) := by group
      _ = x ^ n * (x * y ^ n * ⁅y, x⁆ ^ n) * y * ⁅y, x⁆ ^ (n.choose 2) := by rw [hkey]
      _ = x ^ n * x * y ^ n * (⁅y, x⁆ ^ n * y) * ⁅y, x⁆ ^ (n.choose 2) := by group
      _ = x ^ n * x * y ^ n * (y * ⁅y, x⁆ ^ n) * ⁅y, x⁆ ^ (n.choose 2) := by rw [hcpy]
      _ = x ^ n * x * y ^ n * y * (⁅y, x⁆ ^ n * ⁅y, x⁆ ^ (n.choose 2)) := by group
      _ = x ^ n * x * y ^ n * y * ⁅y, x⁆ ^ (n + n.choose 2) := by rw [pow_add]
      _ = x ^ (n + 1) * y ^ (n + 1) * ⁅y, x⁆ ^ (n + n.choose 2) := by
            rw [← pow_succ x n, mul_assoc (x ^ (n + 1)) (y ^ n) y, ← pow_succ]
      _ = x ^ (n + 1) * y ^ (n + 1) * ⁅y, x⁆ ^ ((n + 1).choose 2) := by
            rw [Nat.choose_succ_succ, Nat.choose_one_right]

/-- **The `p`-th power map is multiplicative.**  If `⁅G, G⁆ ≤ Z(G)`, `p` is an odd prime, and
every commutator has order dividing `p`, then `(x * y) ^ p = x ^ p * y ^ p`. -/
theorem pow_mul_eq_of_class_two {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hclass : (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G) ≤ Subgroup.center G)
    (hcomm : ∀ a b : G, ⁅a, b⁆ ^ p = 1) :
    ∀ x y : G, (x * y) ^ p = x ^ p * y ^ p := by
  intro x y
  rw [pow_mul_eq_of_class_two_aux hclass x y p]
  have hdvd : p ∣ p.choose 2 := by
    obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two hp hodd
    rw [Nat.choose_two_right]
    have hp1 : p - 1 = 2 * k := by omega
    rw [hp1, show p * (2 * k) = (p * k) * 2 by ring, Nat.mul_div_cancel (p * k) (by norm_num)]
    exact dvd_mul_right p k
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, pow_mul, hcomm y x, one_pow, mul_one]

/-! ### Structure of the subgroup of elements of order dividing `p` -/

/-- If `E` is a subgroup consisting exactly of the elements whose `p`-th power is trivial and
every element of `X` differs from a `p`-th root of a central element by such an element, then
`X = Z(X) · E`. -/
theorem top_eq_center_sup {X : Type*} [Group X] {p : ℕ}
    (hpow : ∀ x : X, ∃ z ∈ Subgroup.center X, x ^ p = z ^ p)
    (E : Subgroup X) (hE : ∀ x : X, x ∈ E ↔ x ^ p = 1) :
    (⊤ : Subgroup X) = Subgroup.center X ⊔ E := by
  refine le_antisymm (fun x _ => ?_) le_top
  obtain ⟨z, hz, hzz⟩ := hpow x
  have hEsub : x * z⁻¹ ∈ E := by
    rw [hE]
    have hcz0 : Commute x z := Subgroup.mem_center_iff.mp hz x
    have hcz : Commute x z⁻¹ := hcz0.inv_right
    rw [hcz.mul_pow, inv_pow, hzz, mul_inv_cancel]
  have hx : x = (x * z⁻¹) * z := by group
  rw [hx]
  exact (Subgroup.center X ⊔ E).mul_mem (Subgroup.mem_sup_right hEsub) (Subgroup.mem_sup_left hz)

/-- The centre of a subgroup which together with `Z(X)` generates `X` consists of the elements
of `E` that are central in `X`. -/
theorem centerIn_eq_inf_center {X : Type*} [Group X] {E : Subgroup X}
    (htop : (⊤ : Subgroup X) = Subgroup.center X ⊔ E) :
    Work.PGroup.centerIn E = Subgroup.center X ⊓ E := by
  refine le_antisymm ?_ ?_
  · intro w hw
    obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.mp hw
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro x
      have hx : x ∈ Subgroup.centralizer ({w} : Set X) := by
        have hle : Subgroup.center X ⊔ E ≤ Subgroup.centralizer ({w} : Set X) := by
          refine sup_le ?_ ?_
          · intro z hz
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
            exact Subgroup.mem_center_iff.mp hz w
          · intro e he
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            rw [hy, ← huw]
            have hmem := Subgroup.mem_center_iff.mp hu (⟨e, he⟩ : ↥E)
            exact (congrArg Subtype.val hmem).symm
        have : x ∈ Subgroup.center X ⊔ E := by rw [← htop]; trivial
        exact hle this
      exact (Subgroup.mem_centralizer_iff.mp hx w (Set.mem_singleton w)).symm
    · exact huw ▸ u.2
  · intro z hz
    obtain ⟨hzZ, hzE⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hzE⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro e
    exact Subtype.ext (Subgroup.mem_center_iff.mp hzZ (e : X))

/-- With cyclic centre and derived subgroup of order the prime `p`, the intersection of the
centre with the subgroup of elements of order dividing `p` is precisely the derived subgroup. -/
theorem inf_center_eq_commutator {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hclass : (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) ≤ Subgroup.center X)
    (hcyc : ∃ a : X, Subgroup.center X = Subgroup.zpowers a)
    (hder : Nat.card ↥(⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) = p)
    (E : Subgroup X) (hE : ∀ x : X, x ∈ E ↔ x ^ p = 1) :
    Subgroup.center X ⊓ E = ⁅(⊤ : Subgroup X), ⊤⁆ := by
  set X' : Subgroup X := ⁅(⊤ : Subgroup X), ⊤⁆ with hX'def
  have hcard : Nat.card ↥X' = p := hder
  have hZX : X' ≤ Subgroup.center X := hclass
  have hpow1 : ∀ x ∈ X', x ^ p = 1 := by
    intro x hx
    have h := Subgroup.orderOf_dvd_natCard X' hx
    rw [hcard] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hXE : X' ≤ E := fun x hx => (hE x).mpr (hpow1 x hx)
  have hX'H : X' ≤ Subgroup.center X ⊓ E := le_inf hZX hXE
  refine le_antisymm ?_ hX'H
  intro z hz
  obtain ⟨a, ha⟩ := hcyc
  set H : Subgroup X := Subgroup.center X ⊓ E with hHdef
  have hzH : z ∈ H := hz
  have hHZp : H ≤ Subgroup.zpowers a := fun w hw => ha ▸ (Subgroup.mem_inf.mp hw).1
  haveI : IsCyclic ↥(Subgroup.zpowers a) := isCyclic_zpowers a
  haveI : IsCyclic ↥H := isCyclic_of_le hHZp
  have hexp : Monoid.exponent ↥H ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro h
    refine Subtype.ext ?_
    have hmem : (h : X) ∈ E := (Subgroup.mem_inf.mp h.2).2
    have := (hE (h : X)).mp hmem
    simpa using this
  have hcardH : Nat.card ↥H ∣ p := by
    rw [← IsCyclic.exponent_eq_card (α := ↥H)]
    exact hexp
  have hpcardH : p ∣ Nat.card ↥H := by
    have h := Subgroup.card_dvd_of_le (H := X') (K := H) hX'H
    rwa [hcard] at h
  have heq : Nat.card ↥H = p := Nat.dvd_antisymm hcardH hpcardH
  have hXeqH : X' = H := Subgroup.eq_of_le_of_card_ge hX'H (by rw [heq, hcard])
  rw [hXeqH]
  exact hzH

/-! ### The main theorem -/

theorem centralProduct_of_structure {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hX : IsPGroup p X)
    (hclass : (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) ≤ Subgroup.center X)
    (hcyc : ∃ a : X, Subgroup.center X = Subgroup.zpowers a)
    (hquot : ∀ x : X, x ^ p ∈ Subgroup.center X)
    (hder : Nat.card ↥(⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) = p)
    (hpow : ∀ x : X, ∃ z ∈ Subgroup.center X, x ^ p = z ^ p) :
    ∃ Cc E : Subgroup X, Work.PGroup.IsCentralProduct (⊤ : Subgroup X) Cc E ∧
      (∃ a : X, Cc = Subgroup.zpowers a) ∧
      Work.PGroup.IsExtraspecial p E ∧ Monoid.exponent ↥E ∣ p := by
  have hcommcomp : ∀ a b : X, ⁅a, b⁆ ^ p = 1 := by
    intro a b
    have h := Subgroup.orderOf_dvd_natCard (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X)
      (Subgroup.commutator_mem_commutator (show a ∈ (⊤ : Subgroup X) from trivial)
        (show b ∈ (⊤ : Subgroup X) from trivial))
    rw [hder] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hpowmul : ∀ x y : X, (x * y) ^ p = x ^ p * y ^ p :=
    pow_mul_eq_of_class_two hp hodd hclass hcommcomp
  -- the subgroup of elements of order dividing `p`
  let S : Subgroup X :=
    { carrier := {x : X | x ^ p = 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : a ^ p = 1 := ha
        have hb' : b ^ p = 1 := hb
        show (a * b) ^ p = 1
        rw [hpowmul, ha', hb', one_mul]
      one_mem' := by show (1 : X) ^ p = 1; simp
      inv_mem' := fun {a} ha => by
        have ha' : a ^ p = 1 := ha
        show (a⁻¹) ^ p = 1
        rw [inv_pow, ha', inv_one] }
  let E : Subgroup X := Work.PGroup.omega p 1 (⊤ : Subgroup X)
  have hEeqS : E = S := by
    refine le_antisymm ?_ ?_
    · change Subgroup.closure {y : X | y ∈ (⊤ : Subgroup X) ∧ y ^ (p ^ 1) = 1} ≤ S
      rw [Subgroup.closure_le]
      rintro y ⟨-, hy⟩
      show y ^ p = 1
      simpa using hy
    · intro y hy
      change y ∈ Subgroup.closure {z : X | z ∈ (⊤ : Subgroup X) ∧ z ^ (p ^ 1) = 1}
      have hy' : y ^ p = 1 := hy
      exact Subgroup.subset_closure ⟨trivial, by simpa using hy'⟩
  have hEmem : ∀ x : X, x ∈ E ↔ x ^ p = 1 := by
    intro x
    rw [hEeqS]
    exact Iff.rfl
  have hEpgroup : IsPGroup p E := (hX.of_equiv Subgroup.topEquiv.symm).to_le le_top
  have htop : (⊤ : Subgroup X) = Subgroup.center X ⊔ E := top_eq_center_sup hpow E hEmem
  have hcenterIn : Work.PGroup.centerIn E = (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) := by
    rw [centerIn_eq_inf_center htop,
      inf_center_eq_commutator hp hclass hcyc hder E hEmem]
  have hXE : (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) ≤ E := by
    intro x hx
    rw [hEmem]
    have h := Subgroup.orderOf_dvd_natCard (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) hx
    rw [hder] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  -- `E` is non-abelian
  have hnab : ¬ IsMulCommutative E := by
    intro hcommE
    have hcenterE : Work.PGroup.centerIn E = E := by
      show (Subgroup.center ↥E).map E.subtype = E
      rw [Subgroup.center_eq_top_iff.mpr hcommE, Subgroup.map_top, Subgroup.range_subtype]
    have hXE' : (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) = E := by
      rw [← hcenterIn, hcenterE]
    have hEZ : E ≤ Subgroup.center X := hXE' ▸ hclass
    have htopZ : (⊤ : Subgroup X) ≤ Subgroup.center X := by
      rw [htop]; exact sup_le le_rfl hEZ
    have hZtop : Subgroup.center X = ⊤ := le_antisymm le_top htopZ
    have hab : IsMulCommutative X := Subgroup.center_eq_top_iff.mp hZtop
    have hbot : (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact (isMulCommutative_iff.mp hab x y).symm
    have hcard1 : Nat.card ↥(⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) = 1 :=
      Subgroup.card_eq_one.mpr hbot
    have h1 : p = 1 := by rw [← hder, hcard1]
    have h2 := hp.two_le
    omega
  -- the derived subgroup of `E` is the derived subgroup of `X`
  have hEEne : (⁅E, E⁆ : Subgroup X) ≠ ⊥ := by
    intro hbot
    refine hnab ?_
    rw [isMulCommutative_iff]
    intro a b
    refine Subtype.ext ?_
    have h := commutator_eq_bot_iff_le_centralizer.mp hbot a.2
    exact (Subgroup.mem_centralizer_iff.mp h b.1 b.2).symm
  have hcardEE : Nat.card ↥(⁅E, E⁆ : Subgroup X) = p := by
    have hdvd : Nat.card ↥(⁅E, E⁆ : Subgroup X) ∣ p := by
      have h := Subgroup.card_dvd_of_le
        (Subgroup.commutator_mono (le_top : E ≤ ⊤) (le_top : E ≤ ⊤))
      rwa [hder] at h
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h (fun hc => hEEne (Subgroup.eq_bot_of_card_eq _ hc))
    · exact h
  have hEE' : (⁅E, E⁆ : Subgroup X) = ⁅(⊤ : Subgroup X), ⊤⁆ :=
    Subgroup.eq_of_le_of_card_ge
      (Subgroup.commutator_mono (le_top : E ≤ ⊤) (le_top : E ≤ ⊤))
      (by rw [hcardEE, hder])
  -- the Frattini subgroup of `E` is its centre
  have hfr : Work.PGroup.frattiniIn E = ⁅(⊤ : Subgroup X), ⊤⁆ := by
    rw [Work.PGroup.frattini_eq_agemo_sup_commutator hp E hEpgroup]
    have hag : Work.PGroup.agemo p 1 E = ⊥ := by
      rw [Work.PGroup.agemo]
      refine le_antisymm ?_ bot_le
      rw [Subgroup.closure_le]
      rintro y ⟨x, hx, rfl⟩
      change x ^ (p ^ 1) = 1
      simpa using (hEmem x).mp hx
    rw [hag, bot_sup_eq, hEE']
  have hcenterIn_EE : Work.PGroup.centerIn E = (⁅E, E⁆ : Subgroup X) := by
    rw [hcenterIn, hEE']
  have hcenterIn_fr : Work.PGroup.centerIn E = Work.PGroup.frattiniIn E := by
    rw [hcenterIn, hfr]
  have helem : Work.PGroup.IsElementaryAbelian p (Work.PGroup.centerIn E) := by
    rw [hcenterIn]
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro a b
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hclass a.2) b.1).symm
    · intro x
      refine Subtype.ext ?_
      simpa using (hEmem (x : X)).mp (hXE x.2)
  have hcardcenter : Nat.card ↥(Work.PGroup.centerIn E) = p := by
    rw [hcenterIn]; exact hder
  have hspecial : Work.PGroup.IsSpecial p E := by
    right
    exact ⟨hEpgroup, hnab, hcenterIn_EE, hcenterIn_fr, helem⟩
  have hextraspecial : Work.PGroup.IsExtraspecial p E := ⟨hnab, hspecial, hcardcenter⟩
  have hexpE : Monoid.exponent ↥E ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    exact Subtype.ext ((hEmem (x : X)).mp x.2)
  -- the central product
  have hcenterInZ : Work.PGroup.centerIn (Subgroup.center X) = Subgroup.center X := by
    refine le_antisymm (Work.PGroup.centerIn_le (Subgroup.center X)) ?_
    intro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro e
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (e : X))
  have hcentprod : Work.PGroup.IsCentralProduct (⊤ : Subgroup X) (Subgroup.center X) E := by
    refine ⟨le_top, le_top, htop.symm, ?_, ?_, ?_⟩
    · rw [← le_bot_iff, Subgroup.commutator_le]
      intro z hz e _
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz e).symm
    · rw [hcenterInZ]; exact inf_le_left
    · rw [hcenterIn, inf_center_eq_commutator hp hclass hcyc hder E hEmem]
  exact ⟨Subgroup.center X, E, hcentprod, hcyc, hextraspecial, hexpE⟩

end Work.PGroup.Symplectic

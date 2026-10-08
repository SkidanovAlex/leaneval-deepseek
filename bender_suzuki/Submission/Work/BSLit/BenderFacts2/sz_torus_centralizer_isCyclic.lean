import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2SzDefs
import Submission.Work.BSLit.BenderFacts2.sz_centralizer_involution_eq_U
import Submission.Work.BSLit.BenderFacts2.MyAux.helpers
import Submission.Work.BSLit.BenderFacts2.MyAux.mulAut_eq_inv_of_fixedPointFree
import Submission.Work.BSLit.BenderFacts2.MyAux.eq_of_three_fixedPoints
import Submission.Work.BSLit.BenderFacts2.MyAux.isCyclic_of_le_conj_borel_of_odd
import Submission.Work.BSLit.BenderFacts2.MyAux.isCyclic_centralizer_gl_of_irreducible_minpoly
import Submission.Work.BSLit.BenderFacts2.MyAux.minpoly_irreducible_of_prime_order_dvd_sq_add_one
import Submission.Work.BSLit.BenderFacts2.MyAux.prime_dvd_card_of_fixedPointFree
import Submission.Work.BSLit.BenderFacts2.MyAux.smul_eq_of_mem_of_fixedPoint

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BSLit.BenderFacts2

open LeanEval.GroupTheory.Defs
open scoped Pointwise

/-- If `x ∈ C(u(0,c) * w)` (`c ≠ 0`) is fixed by conjugation by `u(0,c)`, then `x = 1`:
`x` commutes with `u(0,c)` and with `u(0,c) * w`, hence with `w`, so
`x ∈ C(u(0,c)) ⊓ C(w) = U ⊓ C(w) = 1`. -/
theorem eq_one_of_conj_szUgS_eq_self (n : ℕ) (hn : 1 ≤ n) {c : Submission.Sz.SzField n}
    (hc : c ≠ 0) {x : SzModel n}
    (hx : x ∈ Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)))
    (hfix : szUgS n 0 c * x * (szUgS n 0 c)⁻¹ = x) : x = 1 := by
  have hxu : x ∈ Subgroup.centralizer ({szUgS n 0 c} : Set (SzModel n)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z : SzModel n => z * szUgS n 0 c) hfix
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h.symm
  have hu : szUgS n 0 c * x = x * szUgS n 0 c := by
    have h0 : x * szUgS n 0 c = szUgS n 0 c * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxu
    exact h0.symm
  have hxw : x ∈ Subgroup.centralizer ({szWgMS n} : Set (SzModel n)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hg : x * (szUgS n 0 c * szWgMS n) = (szUgS n 0 c * szWgMS n) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    have hu2 : szUgS n 0 c * szUgS n 0 c = 1 := MyAux.szUgS_zero_mul_self n c
    calc x * szWgMS n
        = szUgS n 0 c * (szUgS n 0 c * (x * szWgMS n)) := by
          rw [show szUgS n 0 c * (szUgS n 0 c * (x * szWgMS n))
              = (szUgS n 0 c * szUgS n 0 c) * (x * szWgMS n) from by group, hu2, one_mul]
      _ = szUgS n 0 c * ((szUgS n 0 c * x) * szWgMS n) := by group
      _ = szUgS n 0 c * ((x * szUgS n 0 c) * szWgMS n) := by rw [hu]
      _ = szUgS n 0 c * (x * (szUgS n 0 c * szWgMS n)) := by group
      _ = szUgS n 0 c * ((szUgS n 0 c * szWgMS n) * x) := by rw [hg]
      _ = szWgMS n * x := by
            rw [show szUgS n 0 c * ((szUgS n 0 c * szWgMS n) * x)
                = (szUgS n 0 c * szUgS n 0 c) * (szWgMS n * x) from by group, hu2, one_mul]
  have hxU : x ∈ Submission.Sz.szTwoGroupS n := by
    have h := hxu
    rwa [sz_centralizer_involution_eq_U n hn hc] at h
  have hxinf : x ∈ Submission.Sz.szTwoGroupS n ⊓
      Subgroup.centralizer ({szWgMS n} : Set (SzModel n)) := ⟨hxU, hxw⟩
  rw [MyAux.szTwoGroupS_inf_centralizer_szWgMS n, Subgroup.mem_bot] at hxinf
  exact hxinf

/-- **Every element of `C(u(0,c) * w)` is inverted by `u(0,c)`** (`c ≠ 0`). -/
theorem conj_szUgS_eq_inv_of_mem_centralizer (n : ℕ) (hn : 1 ≤ n)
    {c : Submission.Sz.SzField n} (hc : c ≠ 0) :
    ∀ x ∈ Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)),
      szUgS n 0 c * x * (szUgS n 0 c)⁻¹ = x⁻¹ := by
  set u : SzModel n := szUgS n 0 c with hu
  set g : SzModel n := u * szWgMS n with hg
  set A : Subgroup (SzModel n) := Subgroup.centralizer ({g} : Set (SzModel n)) with hA
  have hu2 : u * u = 1 := MyAux.szUgS_zero_mul_self n c
  have hg_inv : u * g * u⁻¹ = g⁻¹ := MyAux.szUgS_conj_mul_szWgMS n c
  have hmem : ∀ x : ↥A, u * (x : SzModel n) * u⁻¹ ∈ A := by
    intro x
    have hx : (x : SzModel n) * g = g * (x : SzModel n) :=
      Subgroup.mem_centralizer_singleton_iff.mp x.2
    have h1 : (u * (x : SzModel n) * u⁻¹) * g⁻¹ = g⁻¹ * (u * (x : SzModel n) * u⁻¹) := by
      have hconj := congrArg (fun z => u * z * u⁻¹) hx
      rw [show u * ((x : SzModel n) * g) * u⁻¹
            = (u * (x : SzModel n) * u⁻¹) * (u * g * u⁻¹) from by group,
        show u * (g * (x : SzModel n)) * u⁻¹
            = (u * g * u⁻¹) * (u * (x : SzModel n) * u⁻¹) from by group,
        hg_inv] at hconj
      exact hconj
    have h2 : (u * (x : SzModel n) * u⁻¹) * g = g * (u * (x : SzModel n) * u⁻¹) := by
      have h3 : g * (u * (x : SzModel n) * u⁻¹) = (u * (x : SzModel n) * u⁻¹) * g := by
        calc g * (u * (x : SzModel n) * u⁻¹)
            = g * ((u * (x : SzModel n) * u⁻¹) * g⁻¹) * g := by group
          _ = g * (g⁻¹ * (u * (x : SzModel n) * u⁻¹)) * g := by rw [h1]
          _ = (u * (x : SzModel n) * u⁻¹) * g := by group
      exact h3.symm
    show u * (x : SzModel n) * u⁻¹ ∈ Subgroup.centralizer ({g} : Set (SzModel n))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h2
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hmem' : ∀ x : ↥A, u⁻¹ * (x : SzModel n) * u ∈ A := by
    intro x
    simpa [hu_inv] using hmem x
  let α : MulAut ↥A :=
    { toFun := fun x => ⟨u * (x : SzModel n) * u⁻¹, hmem x⟩
      invFun := fun x => ⟨u⁻¹ * (x : SzModel n) * u, hmem' x⟩
      left_inv := fun x => Subtype.ext (by
        show u⁻¹ * (u * (x : SzModel n) * u⁻¹) * u = (x : SzModel n)
        rw [show u⁻¹ * (u * (x : SzModel n) * u⁻¹) * u
            = (u⁻¹ * u) * (x : SzModel n) * (u⁻¹ * u) from by group,
          inv_mul_cancel, one_mul, mul_one])
      right_inv := fun x => Subtype.ext (by
        show u * (u⁻¹ * (x : SzModel n) * u) * u⁻¹ = (x : SzModel n)
        rw [show u * (u⁻¹ * (x : SzModel n) * u) * u⁻¹
            = (u * u⁻¹) * (x : SzModel n) * (u * u⁻¹) from by group,
          mul_inv_cancel, one_mul, mul_one])
      map_mul' := fun x y => Subtype.ext (by
        show u * ((x : SzModel n) * (y : SzModel n)) * u⁻¹
            = (u * (x : SzModel n) * u⁻¹) * (u * (y : SzModel n) * u⁻¹)
        group) }
  have hα : ∀ x : ↥A, α (α x) = x := by
    intro x
    apply Subtype.ext
    show u * (u * (x : SzModel n) * u⁻¹) * u⁻¹ = (x : SzModel n)
    rw [show u * (u * (x : SzModel n) * u⁻¹) * u⁻¹
        = (u * u) * (x : SzModel n) * (u⁻¹ * u⁻¹) from by group, hu_inv]
    simp [hu2]
  have hfix : ∀ x : ↥A, α x = x → x = 1 := by
    intro x hx
    have hx' : u * (x : SzModel n) * u⁻¹ = (x : SzModel n) :=
      congrArg (fun w : ↥A => (w : SzModel n)) hx
    exact Subtype.ext (eq_one_of_conj_szUgS_eq_self n hn hc x.2 hx')
  have hfin := MyAux.mulAut_eq_inv_of_fixedPointFree α hα hfix
  intro x hx
  have h := congrArg (fun w : ↥A => (w : SzModel n)) (hfin ⟨x, hx⟩)
  exact h

/-- **`C(u(0,c) * w)` is abelian** for `c ≠ 0`. -/
theorem commute_of_mem_centralizer_mul_szWgMS (n : ℕ) (hn : 1 ≤ n)
    {c : Submission.Sz.SzField n} (hc : c ≠ 0) :
    ∀ x ∈ Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)),
      ∀ y ∈ Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)),
        x * y = y * x := by
  intro x hx y hy
  have hx' := conj_szUgS_eq_inv_of_mem_centralizer n hn hc x hx
  have hy' := conj_szUgS_eq_inv_of_mem_centralizer n hn hc y hy
  have hxy := conj_szUgS_eq_inv_of_mem_centralizer n hn hc (x * y)
    ((Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n))).mul_mem hx hy)
  have h : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
    have h1 : x⁻¹ * y⁻¹ = szUgS n 0 c * (x * y) * (szUgS n 0 c)⁻¹ := by
      rw [← hx', ← hy']
      group
    rw [h1, hxy, mul_inv_rev]
  have h3 : (x * y)⁻¹ = (y * x)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, h]
  exact inv_inj.mp h3

/-- **`C(u(0,c) * w)` has odd order** for `c ≠ 0`: it contains no element of order `2`. -/
theorem odd_card_centralizer_mul_szWgMS (n : ℕ) (hn : 1 ≤ n)
    {c : Submission.Sz.SzField n} (hc : c ≠ 0) :
    Odd (Nat.card ↥(Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)))) := by
  haveI : Fintype (SzModel n) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)))) 2 h2
  have hxne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hxself : (x : SzModel n)⁻¹ = x := by
    have h : (x : ↥(Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)))) ^ 2 = 1 := by
      simpa [hx2] using pow_orderOf_eq_one x
    have h2' : (x : ↥(Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)))) * x = 1 := by
      rwa [pow_two] at h
    have h3 : (x : SzModel n) * (x : SzModel n) = 1 := by
      have := congrArg (fun w : ↥(Subgroup.centralizer
        ({szUgS n 0 c * szWgMS n} : Set (SzModel n))) => (w : SzModel n)) h2'
      simpa using this
    exact inv_eq_of_mul_eq_one_right h3
  have hfix : szUgS n 0 c * (x : SzModel n) * (szUgS n 0 c)⁻¹ = (x : SzModel n) := by
    rw [conj_szUgS_eq_inv_of_mem_centralizer n hn hc (x : SzModel n) x.2, hxself]
  exact hxne (Subtype.ext (eq_one_of_conj_szUgS_eq_self n hn hc x.2 hfix))

/-- **The centralizer in `Sz(2^(2n+1))` of `u(0,c) * w` (`c ≠ 0`) is cyclic.**

It is abelian of odd order, and `u(0,c)` inverts it.  Let `b` be an element of prime order `ℓ` of
this centralizer `A`.  If `b` has a fixed point on the Bender action, then `A` fixes that point
and hence lies in a conjugate of the Borel `B = U ⋊ T`, where it embeds in the cyclic torus `T`.
Otherwise `b` is fixed-point-free, every `⟨b⟩`-orbit has size `ℓ`, so `ℓ ∣ q² + 1`; then the
minimal polynomial of `b` over `F_q` is irreducible of degree `4`, `F_q[b]` is the field
`F_{q⁴}`, and the centralizer of `b` in `GL₄(F_q)` is isomorphic to `F_{q⁴}ˣ`, hence cyclic. -/
theorem sz_torus_centralizer_isCyclic (n : ℕ) (hn : 1 ≤ n)
    {c : Submission.Sz.SzField n} (hc : c ≠ 0) :
    IsCyclic ↥(Subgroup.centralizer
      (singleton (Work.BSLit.BenderFacts2.szUgS n 0 c *
        Work.BSLit.BenderFacts2.szWgMS n) :
        Set (LeanEval.GroupTheory.Defs.SzModel n))) := by
  haveI : Fintype (SzModel n) := Fintype.ofFinite _
  set A : Subgroup (SzModel n) :=
    Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)) with hA
  have habel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    commute_of_mem_centralizer_mul_szWgMS n hn hc
  have hodd : Odd (Nat.card ↥A) := odd_card_centralizer_mul_szWgMS n hn hc
  by_cases hbot : A = ⊥
  · rw [hbot]
    infer_instance
  · have hex : ∃ x ∈ A, x ≠ 1 := by
      by_contra h
      exact hbot ((Subgroup.eq_bot_iff_forall A).mpr (fun x hx => by
        by_contra hx1
        exact h ⟨x, hx, hx1⟩))
    obtain ⟨a, haA, ha1⟩ := hex
    have haord : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
    obtain ⟨ℓ, hℓprime, hℓdvd⟩ := Nat.exists_prime_and_dvd haord
    have hdvd' : ℓ ∣ Nat.card ↥(Subgroup.zpowers a) := by rwa [Nat.card_zpowers]
    haveI : Fact (Nat.Prime ℓ) := ⟨hℓprime⟩
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.zpowers a)) ℓ hdvd'
    set b : SzModel n := (y : SzModel n) with hb
    have hbA : b ∈ A := Subgroup.zpowers_le.mpr haA y.2
    have hbord : orderOf b = ℓ := (Subgroup.orderOf_coe y).trans hyord
    have hb1 : b ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hbord
      exact hℓprime.ne_one hbord.symm
    by_cases hfixed : ∃ ω : SzModel n ⧸ Submission.Sz.szBorelS n, b • ω = ω
    · obtain ⟨ω, hω⟩ := hfixed
      obtain ⟨h, hh⟩ : ∃ h : SzModel n, ω = h • Submission.Sz.szPtBase n := by
        induction ω using Quotient.inductionOn with
        | h g =>
            refine ⟨g, ?_⟩
            rw [show Submission.Sz.szPtBase n
                = ((1 : SzModel n) : SzModel n ⧸ Submission.Sz.szBorelS n) from rfl,
              Commons.GroupTheory.GroupAction.coset_smul_mk (Submission.Sz.szBorelS n) g 1,
              mul_one]
      have hstab : MulAction.stabilizer (SzModel n) ω
          = (Submission.Sz.szBorelS n).map (MulAut.conj h).toMonoidHom := by
        rw [hh, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
          MulAction.stabilizer_quotient]
      have hfixA : ∀ x ∈ A, x • ω = ω :=
        MyAux.smul_eq_of_mem_of_fixedPoint n hn hbA hb1 habel hodd hω
      have hAle : A ≤ (Submission.Sz.szBorelS n).map (MulAut.conj h).toMonoidHom := by
        rw [← hstab]
        intro x hx
        rw [MulAction.mem_stabilizer_iff]
        exact hfixA x hx
      exact MyAux.isCyclic_of_le_conj_borel_of_odd n hAle hodd
    · push_neg at hfixed
      haveI : Fintype ((SzModel n) ⧸ Submission.Sz.szBorelS n) := Fintype.ofFinite _
      have hdvdΩ : ℓ ∣ Nat.card ((SzModel n) ⧸ Submission.Sz.szBorelS n) := by
        refine MyAux.prime_dvd_card_of_fixedPointFree hℓprime (E := Subgroup.zpowers b) ?_ ?_
        · rw [Nat.card_zpowers, hbord]
        · intro x ω hxω
          by_contra hxne
          have hxord : orderOf (x : SzModel n) = ℓ := by
            have hdvd : orderOf (x : SzModel n) ∣ ℓ := by
              rw [← hbord]
              exact orderOf_dvd_of_mem_zpowers x.2
            rcases (Nat.dvd_prime hℓprime).mp hdvd with h1 | h1
            · exact absurd h1 (fun h => hxne (Subtype.ext (orderOf_eq_one_iff.mp h)))
            · exact h1
          have hspan : Subgroup.zpowers (x : SzModel n) = Subgroup.zpowers b := by
            refine Subgroup.eq_of_le_of_card_ge ?_ ?_
            · rw [Subgroup.zpowers_le]
              exact x.2
            · rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hbord]
          have hbω : b • ω = ω := by
            have hxmem : b ∈ Subgroup.zpowers (x : SzModel n) := by
              rw [hspan]
              exact Subgroup.mem_zpowers b
            have hxstab : (x : SzModel n) ∈ MulAction.stabilizer (SzModel n) ω := by
              rw [MulAction.mem_stabilizer_iff]
              exact hxω
            exact (Subgroup.zpowers_le.mpr hxstab) hxmem
          exact hfixed ω hbω
      have hdvd : ℓ ∣ Nat.card (Submission.Sz.SzField n) ^ 2 + 1 := by
        rwa [Submission.Sz.card_quotient_szBorelS] at hdvdΩ
      have hℓodd : Odd ℓ := by
        refine Odd.of_dvd_nat ?_ hdvd
        rw [Submission.Sz.card_szField n, ← pow_mul,
          show (2 * n + 1) * 2 = 4 * n + 2 from by ring]
        simpa [show 4 * n + 2 = (4 * n + 1) + 1 from by ring] using
          Submission.Sz.odd_two_pow_add_one (4 * n + 1)
      have hbordGL : orderOf ((b : GL (Fin 4) (Submission.Sz.SzField n))) = ℓ := by
        rw [Subgroup.orderOf_coe, hbord]
      have hkey := MyAux.minpoly_irreducible_of_prime_order_dvd_sq_add_one
        (F := Submission.Sz.SzField n) (b : GL (Fin 4) (Submission.Sz.SzField n))
        hℓprime hℓodd hbordGL hdvd
      haveI hcycGL : IsCyclic ↥(Subgroup.centralizer
          ({(b : GL (Fin 4) (Submission.Sz.SzField n))} :
            Set (GL (Fin 4) (Submission.Sz.SzField n)))) :=
        MyAux.isCyclic_centralizer_gl_of_irreducible_minpoly _ hkey.1 hkey.2
      have hcyc : IsCyclic ↥(Subgroup.centralizer ({b} : Set (SzModel n))) := by
        haveI : IsCyclic ↥((Subgroup.centralizer ({b} : Set (SzModel n))).map
            (SzModel n).subtype) :=
          Subgroup.isCyclic_of_le (by
            rintro y ⟨x, hx, rfl⟩
            have hx' : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hx
            rw [Subgroup.mem_centralizer_singleton_iff]
            simpa using congrArg
              (fun z : SzModel n => (z : GL (Fin 4) (Submission.Sz.SzField n))) hx')
        exact (Subgroup.equivMapOfInjective (Subgroup.centralizer ({b} : Set (SzModel n)))
          (SzModel n).subtype (SzModel n).subtype_injective).isCyclic.mpr inferInstance
      have hAle : A ≤ Subgroup.centralizer ({b} : Set (SzModel n)) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact habel x hx b hbA
      exact Subgroup.isCyclic_of_le hAle

end Work.BSLit.BenderFacts2

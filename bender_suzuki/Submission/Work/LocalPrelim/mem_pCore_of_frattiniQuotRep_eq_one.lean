import Mathlib
import Submission.Work.LocalPrelim.Ft72Rep
import Submission.Work.LocalPrelim.Ft72Util
import Submission.Work.Fitting.centralizer_pPrimePCore_le
import Submission.Work.Coprime.trivial_of_trivial_on_frattiniQuotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement IsMulCommutative

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.LocalPrelim

/-- If an element acts trivially through the representation `frattiniQuotRep` then it acts
trivially on the Frattini quotient `↥F ⧸ Φ(↥F)`. -/
lemma frattiniQuotConj_eq_one_of_frattiniQuotRep_eq_one {X : Type*} [Group X] {p : ℕ}
    {F : Subgroup X} [F.Normal]
    [IsMulCommutative (↥F ⧸ frattini ↥F)] [Fact (∀ x : ↥F ⧸ frattini ↥F, x ^ p = 1)]
    {y : X} (h : frattiniQuotRep p F y = 1) : frattiniQuotConj F y = 1 := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H z =>
    rw [frattiniQuotConj_apply_mk, MulAut.one_apply]
    have h1 : frattiniQuotRep p F y (Additive.ofMul (↑z : ↥F ⧸ frattini ↥F))
        = Additive.ofMul (↑z : ↥F ⧸ frattini ↥F) := by
      rw [h]; rfl
    rw [frattiniQuotRep_apply_ofMul] at h1
    exact Additive.ofMul.injective h1

/-- Membership form: if `y` acts trivially on `↥F ⧸ Φ(↥F)` then for every `z : ↥F` the
commutator `z⁻¹ * (conj y z)` lies in `Φ(↥F)`. -/
lemma mem_frattini_of_frattiniQuotConj_eq_one {X : Type*} [Group X] {F : Subgroup X} [F.Normal]
    {y : X} (h : frattiniQuotConj F y = 1) (z : ↥F) :
    z⁻¹ * MulAut.conjNormal y z ∈ frattini ↥F := by
  have h' : (↑z : ↥F ⧸ frattini ↥F) = ↑(MulAut.conjNormal y z) := by
    rw [← frattiniQuotConj_apply_mk F y z, h, MulAut.one_apply]
  rwa [QuotientGroup.eq] at h'

/-- The kernel of the conjugation representation of `X` on `O_p(X)/Φ(O_p(X))` is contained in
`O_p(X)`. -/
private theorem ker_frattiniQuotRep_le {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hps : Work.Fitting.IsPSolvable p X)
    (hcore : Work.Fitting.pPrimeCore p X = ⊥)
    [IsMulCommutative (↥(Work.Fitting.pCore p X) ⧸ frattini ↥(Work.Fitting.pCore p X))]
    [Fact (∀ x : ↥(Work.Fitting.pCore p X) ⧸ frattini ↥(Work.Fitting.pCore p X), x ^ p = 1)] :
    (frattiniQuotRep p (Work.Fitting.pCore p X)).ker ≤ Work.Fitting.pCore p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Work.Fitting.IsPSolvable p X := hps
  let F : Subgroup X := Work.Fitting.pCore p X
  haveI hFnorm : F.Normal := inferInstance
  haveI hFfin : Finite ↥F := inferInstance
  have hFp : IsPGroup p ↥F := Work.Fitting.isPGroup_pCore (G := X) hp
  have hcent : Subgroup.centralizer (F : Set X) ≤ F :=
    Work.Fitting.centralizer_pCore_le_of_pPrimeCore_eq_bot p X hp hcore
  let K : Subgroup X := (frattiniQuotRep p F).ker
  have hKnorm : K.Normal := MonoidHom.normal_ker (frattiniQuotRep p F)
  -- key step: an element of `K` of prime order `q ≠ p` centralizes `F`
  have hkey : ∀ c : X, c ∈ K → ∀ q : ℕ, q.Prime → orderOf c = q → q ≠ p →
      c ∈ Subgroup.centralizer (F : Set X) := by
    intro c hcK q hq hcq hqne
    have hrc : frattiniQuotRep p F c = 1 := MonoidHom.mem_ker.mp hcK
    letI hconj : MulDistribMulAction X ↥F :=
      { smul := fun x y => MulAut.conjNormal x y
        one_smul := fun y => by
          show MulAut.conjNormal (1 : X) y = y
          rw [map_one]; exact MulAut.one_apply ↥F y
        mul_smul := fun x y z => by
          show MulAut.conjNormal (x * y) z = MulAut.conjNormal x (MulAut.conjNormal y z)
          rw [map_mul, MulAut.mul_apply]
        smul_one := fun x => by
          show MulAut.conjNormal x (1 : ↥F) = 1
          exact map_one (MulAut.conjNormal x)
        smul_mul := fun x y z => by
          show MulAut.conjNormal x (y * z) = MulAut.conjNormal x y * MulAut.conjNormal x z
          exact map_mul (MulAut.conjNormal x) y z }
    let A : Subgroup X := Subgroup.zpowers c
    letI : MulDistribMulAction ↥A ↥F :=
      MulDistribMulAction.compHom ↥F (Subgroup.subtype A)
    have hsmul : ∀ (a : ↥A) (y : ↥F), a • y = MulAut.conjNormal (↑a : X) y := fun a y => rfl
    have hcop : (Nat.card ↥A).Coprime (Nat.card ↥F) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hFp
      rw [Nat.card_zpowers, hcq, hk]
      exact Nat.Coprime.pow_right k ((hq.coprime_iff_not_dvd).mpr
        (fun h => hqne ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)))
    have hcomm : FT.commutator ↥A (⊤ : Subgroup ↥F) ≤ frattini ↥F := by
      refine FT.commutator_le fun a y hy => ?_
      show y⁻¹ * MulAut.conjNormal (↑a : X) y ∈ frattini ↥F
      have haK : (↑a : X) ∈ K := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
        rw [← hk]
        exact Subgroup.zpow_mem K hcK k
      have hconj' : frattiniQuotConj F (↑a) = 1 :=
        frattiniQuotConj_eq_one_of_frattiniQuotRep_eq_one (MonoidHom.mem_ker.mp haK)
      exact mem_frattini_of_frattiniQuotConj_eq_one hconj' y
    have htriv : FT.IsTrivialOn ↥A ↥F :=
      Work.Coprime.trivial_of_trivial_on_frattiniQuotient ↥A hcop p hFp hcomm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := htriv ⟨c, Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one c⟩⟩ (⟨y, hy⟩ : ↥F)
    have h' : MulAut.conjNormal c (⟨y, hy⟩ : ↥F) = (⟨y, hy⟩ : ↥F) := h
    have h2 : c * y * c⁻¹ = y := by
      simpa using congrArg (Subtype.val) h'
    calc y * c = (c * y * c⁻¹) * c := by rw [h2]
      _ = c * y := by group
  -- every prime divisor of `|K|` is `p`
  refine Work.Fitting.le_piCore hKnorm ?_
  intro q hq hdvd
  by_contra hqne
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) q hdvd
  have hord : orderOf ((x₀ : X)) = q := by
    rw [Subgroup.orderOf_coe, hx₀]
  have hcC : (x₀ : X) ∈ Subgroup.centralizer (F : Set X) :=
    hkey (x₀ : X) x₀.2 q hq hord hqne
  have hcF : (x₀ : X) ∈ F := hcent hcC
  have hdvdF : q ∣ Nat.card ↥F := by
    have h1 : Nat.card ↥(Subgroup.zpowers (x₀ : X)) ∣ Nat.card ↥F :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcF)
    rwa [Nat.card_zpowers, hord] at h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hFp
  rw [hk] at hdvdF
  exact hqne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvdF))

/-- **Faithfulness of the `O_p/Φ`-action.**  If `O_{p'}(X) = 1` and `X` is `p`-solvable, then an
element acting trivially on `O_p(X)/Φ(O_p(X))` lies in `O_p(X)`.

Setup: here `frattiniQuotRep p F` (see `Submission/Work/LocalPrelim/Ft72Rep.lean`) is the
conjugation representation of `X` over `ZMod p` on the `ZMod p`-space `Additive (↥F ⧸ Φ(↥F))`,
with `frattiniQuotRep_apply_ofMul : ρ x (Additive.ofMul y) = Additive.ofMul (MulAut.conjNormal x y)`
and `frattiniQuotConj_eq_one_of_mem` (in `Ft72Util.lean`).

Proof sketch.  Let `F := Work.Fitting.pCore p X` and `K := (frattiniQuotRep p F).ker ⊴ X`
(`MonoidHom.normal_ker`); `hx` says `x ∈ K`.  Show `K ≤ F`.

* `hcent : Subgroup.centralizer (F : Set X) ≤ F` is
  `Work.Fitting.centralizer_pCore_le_of_pPrimeCore_eq_bot p X hp hcore`.
* Suppose some prime `q ≠ p` divides `Nat.card K`.  Cauchy (`exists_prime_orderOf_dvd_card'`) gives
  `c ∈ K` with `orderOf c = q`.  Since `c` acts trivially on `F/Φ(F)`, for `y : ↥F` we get
  `↑(MulAut.conjNormal c y) = ↑y`, i.e. `y⁻¹ * (MulAut.conjNormal c y) ∈ frattini ↥F`
  (`QuotientGroup.eq`).  Apply `Work.Coprime.trivial_of_trivial_on_frattiniQuotient`
  (or `Work.Coprime.mem_centralizer_of_commutator_le_frattini`-style reasoning) to the group
  `A := ↥(Subgroup.zpowers c)` acting on `↥F` by conjugation: build the
  `MulDistribMulAction ↥(Subgroup.zpowers c) ↥F` instance with `a • y := MulAut.conjNormal ((a : X)) y`
  (prove its fields with `MulAut.conjNormal.map_one`, `MulAut.conjNormal.map_mul`,
  `MulAut.one_apply`, `MulAut.mul_apply`, `map_mul`).  Coprimality:
  `Nat.card_zpowers : Nat.card ↥(Subgroup.zpowers c) = orderOf c = q` and `Nat.card ↥F = p ^ k` for
  some `k` (`IsPGroup.iff_card`), and `q ≠ p` is prime.  The hypothesis
  `FT.commutator A ⊤ ≤ frattini ↥F` follows with `FT.commutator_le`, reducing `a ∈ Subgroup.zpowers c`
  to the case `a = c` using `Subgroup.mem_zpowers_iff` and `map_pow`.
  Conclusion: `c ∈ Subgroup.centralizer (F : Set X) ≤ F`, so `q ∣ Nat.card ↥F = p ^ k`, so `q = p`,
  contradiction.
* Therefore every prime divisor of `Nat.card K` equals `p`, so `Nat.card K = p ^ k`
  (`Nat.eq_prime_pow_of_unique_prime_dvd`), so `K` is a `p`-group (`IsPGroup.iff_card`) and hence
  `K ≤ Work.Fitting.pCore p X` (`K` is normal, use `Work.Fitting.le_pCore` with
  `Work.Fitting.isPiNat_prime_iff_isPGroup`).

Do NOT import `Submission.Work.LocalPrelim.mem_centralizer_of_commutator_le_frattini`
(it still contains a `sorry`). -/
theorem mem_pCore_of_frattiniQuotRep_eq_one {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hps : Work.Fitting.IsPSolvable p X)
    (hcore : Work.Fitting.pPrimeCore p X = ⊥)
    [IsMulCommutative (↥(Work.Fitting.pCore p X) ⧸ frattini ↥(Work.Fitting.pCore p X))]
    [Fact (∀ x : ↥(Work.Fitting.pCore p X) ⧸ frattini ↥(Work.Fitting.pCore p X), x ^ p = 1)]
    {x : X} (hx : Work.LocalPrelim.frattiniQuotRep p (Work.Fitting.pCore p X) x = 1) :
    x ∈ Work.Fitting.pCore p X :=
  ker_frattiniQuotRep_le hp hps hcore (MonoidHom.mem_ker.mpr hx)

end Work.LocalPrelim

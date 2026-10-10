import Mathlib.Tactic.Group
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Inflating an invariant continuous character along a normal subgroup

Let `G` be a topological group, `N ◁ G` a normal subgroup with `[G : N] = d` coprime
to a prime `q`, and `z : N → ZMod q` an additive map which is invariant under
conjugation by `G` (i.e. `z (σ τ σ⁻¹) = z τ`) and continuous in the sense that it
vanishes on an open subgroup of `N`.

Then `z` extends to an additive (hence continuous) map `η : G → ZMod q`.

The algebraic part is the classical *transfer* argument: averaging the conjugated
values of `z` over the cosets of `N` in `G` produces a homomorphism `G → ZMod q`
which restricts to `d • z` on `N`; since `d` is invertible modulo `q`, it can be
rescaled to extend `z` itself.

The topological part uses the extra freedom gained from the extension: for every
`g : G` the element `g ^ d` lies in `N`, and `z (g ^ d) = d • η g`; since `d` is a
unit modulo `q`, `ker η = {g | g ^ d ∈ ker z}`, which is open because `g ↦ g ^ d`
is continuous and `ker z` is open in `N`.
-/

namespace Work.HRec

open QuotientGroup

set_option linter.style.haveILetI false

noncomputable section

/-! ### The transfer construction -/

/-- A (non-canonical) section of the quotient map `G → G ⧸ N`. -/
def sec (G : Type*) [Group G] (N : Subgroup G) [N.Normal] : G ⧸ N → G :=
  fun q => (QuotientGroup.mk_surjective q).choose

lemma sec_spec (G : Type*) [Group G] (N : Subgroup G) [N.Normal] (q : G ⧸ N) :
    QuotientGroup.mk (sec G N q) = q := (QuotientGroup.mk_surjective q).choose_spec

lemma smul_eq_mk_mul (G : Type*) [Group G] (N : Subgroup G) [N.Normal] (g : G) (x : G ⧸ N) :
    g • x = QuotientGroup.mk g * x := by
  conv_lhs => rw [← sec_spec G N x]
  rw [show g • (QuotientGroup.mk (sec G N x) : G ⧸ N) = QuotientGroup.mk (g * sec G N x) from rfl,
    QuotientGroup.mk_mul, sec_spec G N x]

lemma delta_mem (G : Type*) [Group G] (N : Subgroup G) [N.Normal] (g : G) (x : G ⧸ N) :
    (sec G N (g • x))⁻¹ * g * sec G N x ∈ N := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    sec_spec G N (g • x), sec_spec G N x, smul_eq_mk_mul]
  group

/-- The element of `N` measuring the failure of the chosen coset representatives
to be multiplicative: if `g • x = (mk g) * x` and `sec` is a section, then
`sec (g • x)` and `g * sec x` differ by the element `delta g x ∈ N`. -/
def delta (G : Type*) [Group G] (N : Subgroup G) [N.Normal] (g : G) (x : G ⧸ N) : N :=
  ⟨(sec G N (g • x))⁻¹ * g * sec G N x, delta_mem G N g x⟩

lemma delta_mul (G : Type*) [Group G] (N : Subgroup G) [N.Normal] (g h : G) (x : G ⧸ N) :
    delta G N (g*h) x = delta G N g (h • x) * delta G N h x := by
  apply Subtype.ext
  simp only [delta, Subgroup.coe_mul]
  rw [mul_smul]
  group

/-- **Transfer step.** If `z : N → ZMod q` is additive and invariant under conjugation,
then it extends to an additive map `G → ZMod q` whenever `[G : N] = d` is invertible
modulo `q`. -/
theorem exists_additive_extension (G : Type*) [Group G] (N : Subgroup G) [N.Normal]
    (q d : ℕ) (hq : q.Prime) (hd : Nat.card (G ⧸ N) = d) (hdq : Nat.Coprime d q)
    (z : N → ZMod q) (hzadd : ∀ a b : N, z (a * b) = z a + z b)
    (hinv : ∀ (σ : G) (τ : N) (h : σ * (τ : G) * σ⁻¹ ∈ N),
      z ⟨σ * (τ : G) * σ⁻¹, h⟩ = z τ) :
    ∃ η : G → ZMod q, (∀ a b : G, η (a * b) = η a + η b) ∧
      (∀ τ : N, η (τ : G) = z τ) := by
  have hd0 : d ≠ 0 := fun h0 => hq.ne_one ((Nat.coprime_zero_left q).mp (h0 ▸ hdq))
  haveI : Finite (G ⧸ N) := (Nat.card_ne_zero.mp (by rw [hd]; exact hd0)).2
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ N) = d := by rw [← Nat.card_eq_fintype_card, hd]
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime d hdq
  have hu : (u : ZMod q) = (d : ZMod q) := ZMod.coe_unitOfCoprime d hdq
  let w : (ZMod q)ˣ := u⁻¹
  have hwu : (w : ZMod q) * (u : ZMod q) = 1 := by simp [w]
  let eta : G → ZMod q := fun g => (w : ZMod q) * ∑ x : G ⧸ N, z (delta G N g x)
  refine ⟨eta, ?_, ?_⟩
  · intro a b
    show (w : ZMod q) * (∑ x : G ⧸ N, z (delta G N (a*b) x)) =
      (w : ZMod q) * (∑ x : G ⧸ N, z (delta G N a x)) +
      (w : ZMod q) * (∑ x : G ⧸ N, z (delta G N b x))
    have h1 : ∀ x : G ⧸ N,
        z (delta G N (a*b) x) = z (delta G N a (b • x)) + z (delta G N b x) :=
      fun x => by rw [delta_mul, hzadd]
    have h2 : (∑ x : G ⧸ N, z (delta G N a (b • x))) = ∑ x : G ⧸ N, z (delta G N a x) :=
      Fintype.sum_equiv (MulAction.toPerm b)
        (fun x => z (delta G N a (b • x))) (fun x => z (delta G N a x)) (fun x => rfl)
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_add_distrib, h2, mul_add]
  · intro τ
    have hterm : ∀ x : G ⧸ N, z (delta G N (τ : G) x) = z τ := by
      intro x
      have hx : (τ : G) • x = x := by
        rw [smul_eq_mk_mul, (QuotientGroup.eq_one_iff (τ : G)).mpr τ.2, one_mul]
      have hmem : (sec G N x)⁻¹ * (τ : G) * ((sec G N x)⁻¹)⁻¹ ∈ N := by
        have h : (sec G N ((τ:G) • x))⁻¹ * (τ:G) * sec G N x ∈ N := (delta G N (τ:G) x).2
        rw [hx] at h
        simpa [inv_inv] using h
      have hdelta : delta G N (τ : G) x =
          ⟨(sec G N x)⁻¹ * (τ : G) * ((sec G N x)⁻¹)⁻¹, hmem⟩ := by
        apply Subtype.ext
        simp only [delta]
        rw [hx, inv_inv]
      rw [hdelta]
      exact hinv ((sec G N x)⁻¹) τ _
    show (w : ZMod q) * (∑ x : G ⧸ N, z (delta G N (τ : G) x)) = z τ
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ, hcard,
      nsmul_eq_mul, ← hu, ← mul_assoc, hwu, one_mul]

/-! ### Continuity of the extension -/

/-- If `z : N → ZMod q` vanishes on an open subgroup of `N` and `η : G → ZMod q` is an
additive extension of `z` with `[G : N] = d` coprime to `q`, then `η` is continuous
(equivalently, vanishes on an open subgroup of `G`). -/
theorem exists_isOpen_vanishing (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (q d : ℕ) (hd : Nat.card (G ⧸ N) = d) (hdq : Nat.Coprime d q)
    (z : N → ZMod q) (hzadd : ∀ a b : N, z (a*b) = z a + z b)
    (hzcont : ∃ U : Subgroup N, IsOpen (U:Set N) ∧ ∀ x ∈ U, z x = 0)
    (η : G → ZMod q) (hηadd : ∀ a b : G, η (a*b) = η a + η b) (hηext : ∀ τ : N, η (τ:G) = z τ) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ x ∈ U, η x = 0 := by
  have hz1 : z 1 = 0 := by
    have h := hzadd 1 1
    rw [mul_one] at h
    have h2 : z 1 + 0 = z 1 + z 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have hz_inv : ∀ x : N, z x⁻¹ = - z x := by
    intro x
    have h := hzadd x x⁻¹
    rw [mul_inv_cancel, hz1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  let K : Subgroup N :=
    { carrier := {x | z x = 0}
      one_mem' := hz1
      mul_mem' := fun {a b} ha hb => by
        change z (a * b) = 0
        rw [hzadd, ha, hb, add_zero]
      inv_mem' := fun {x} ha => by
        change z x⁻¹ = 0
        rw [hz_inv, ha, neg_zero] }
  have hKopen : IsOpen (K : Set N) := by
    obtain ⟨U, hUo, hUz⟩ := hzcont
    exact Subgroup.isOpen_mono (fun x hx => hUz x hx) hUo
  have hidx : N.index = d := by rw [Subgroup.index_eq_card, hd]
  have hgd : ∀ g : G, g ^ d ∈ N := fun g => hidx ▸ Subgroup.pow_index_mem N g
  let Φ : G → N := fun g => ⟨g ^ d, hgd g⟩
  have hΦcont : Continuous Φ := (continuous_pow d).subtype_mk _
  have hη1 : η 1 = 0 := by
    have h := hηadd 1 1
    rw [mul_one] at h
    have h2 : η 1 + 0 = η 1 + η 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have hηpow : ∀ (g : G) (n : ℕ), η (g ^ n) = n • η g := by
    intro g n
    induction n with
    | zero => simp [hη1]
    | succ k ih => rw [pow_succ, hηadd, ih, succ_nsmul]
  have hzΦ : ∀ g : G, z (Φ g) = d • η g := by
    intro g
    rw [← hηext (Φ g)]
    exact hηpow g d
  have hunit : IsUnit (d : ZMod q) := (ZMod.isUnit_iff_coprime d q).mpr hdq
  have hkey : ∀ g : G, η g = 0 ↔ Φ g ∈ K := by
    intro g
    have hzm : z (Φ g) = (d : ZMod q) * η g := by rw [hzΦ, nsmul_eq_mul]
    rw [show (Φ g ∈ K) ↔ z (Φ g) = 0 from Iff.rfl, hzm, IsUnit.mul_right_eq_zero hunit]
  let U : Subgroup G :=
    { carrier := {g | η g = 0}
      one_mem' := hη1
      mul_mem' := fun {a b} ha hb => by
        change η (a * b) = 0
        rw [hηadd, ha, hb, add_zero]
      inv_mem' := fun {x} hx => by
        change η x⁻¹ = 0
        have h := hηadd x x⁻¹
        rw [mul_inv_cancel, hη1] at h
        rw [eq_neg_of_add_eq_zero_right h.symm, hx, neg_zero] }
  refine ⟨U, ?_, fun x hx => hx⟩
  have hset : (U : Set G) = Φ ⁻¹' (K : Set N) := funext fun g => propext (hkey g)
  rw [hset]
  exact hKopen.preimage hΦcont

/-! ### The main statement -/

theorem exists_inflated_of_invariant (q : ℕ) (hq : q.Prime)
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (d : ℕ) (hd : Nat.card (G ⧸ N) = d) (hdq : Nat.Coprime d q)
    (z : N → ZMod q) (hzadd : ∀ a b : N, z (a * b) = z a + z b)
    (hzcont : ∃ U : Subgroup N, IsOpen (U : Set N) ∧ ∀ x ∈ U, z x = 0)
    (hinv : ∀ (σ : G) (τ : N) (h : σ * (τ : G) * σ⁻¹ ∈ N),
      z ⟨σ * (τ : G) * σ⁻¹, h⟩ = z τ) :
    ∃ η : G → ZMod q, (∀ a b : G, η (a * b) = η a + η b) ∧
      (∀ τ : N, η (τ : G) = z τ) ∧
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ x ∈ U, η x = 0 := by
  obtain ⟨η, hadd, hext⟩ := exists_additive_extension G N q d hq hd hdq z hzadd hinv
  obtain ⟨U, hUo, hUz⟩ := exists_isOpen_vanishing G N q d hd hdq z hzadd hzcont η hadd hext
  exact ⟨η, hadd, hext, U, hUo, hUz⟩

end

end Work.HRec

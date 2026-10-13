import Mathlib
import Submission.Work.DSG4b.rootLocal_flat

/-!
# `gonfPerfect` — perfectification of a commutative local ring: vocabulary

This file sets up the tower whose colimit perfectifies a local ring `R` (no Noetherian hypothesis).

Let `k = R/𝔪` be the residue field and suppose `k` has characteristic a prime `p`.  Choose a
`p`-basis `Λ ⊆ k` of `k` over `k^p` (monomials with exponents `< p` form a `k^p`-basis of `k`) and
lifts `b̃_j ∈ R` of the elements `j ∈ Λ`.  The `N`-th stage is

`AN D N = R[T_j : j ∈ Λ] ⧸ (T_j^{p^N} - b̃_j)`,

a free `R`-module (hence flat) with `R`-basis the reduced monomials of exponent `< p^N`; the
transition `AN D i →+* AN D j` (`i ≤ j`) is `T_j ↦ T_j^{p^{j-i}}`, and `S D` is the colimit.  The
residue field of `S D` is the perfect closure `PC = k^{perf}` of `k`: the maps
`tauN D N : AN D N →+* PC`, `T_j ↦ b̃_j^{1/p^N}`, assemble into a ring homomorphism
`psi D : S D →+* PC` whose kernel is `𝔪 · S D`.
-/

namespace Work.DSG4b.gonfPerfect

universe u

open MvPolynomial Polynomial

/-- Data needed to perfectify a local ring `R` at a prime `p`: a `p`-basis `Λ` of the residue field
`k = R/𝔪` over `k^p`, exhibited by the monomial basis of `k` over `k^p`, together with a lift
`Λ → R` of the residue map. -/
structure PData (R : Type u) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] where
  /-- the `p`-basis of the residue field -/
  pB : Set (IsLocalRing.ResidueField R)
  /-- the monomial basis of `k` over `k ^ p` -/
  basis : Module.Basis {e : pB →₀ ℕ // ∀ a : pB, e a < p}
    ((frobenius (IsLocalRing.ResidueField R) p).fieldRange) (IsLocalRing.ResidueField R)
  /-- the basis vectors are the monomials -/
  basis_apply : ∀ e, (basis e : IsLocalRing.ResidueField R) =
    e.1.prod (fun a k => (a : IsLocalRing.ResidueField R) ^ k)
  /-- a lift of the `p`-basis to `R` -/
  lift : pB → R
  /-- the lift is a lift -/
  lift_spec : ∀ b, IsLocalRing.residue R (lift b) = (b : IsLocalRing.ResidueField R)

namespace PData

variable {R : Type u} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime]
variable [CharP (IsLocalRing.ResidueField R) p]

/-- The perfect closure of the residue field of `R`; this is the residue field of the colimit. -/
abbrev PC (D : PData R p) : Type u := PerfectClosure (IsLocalRing.ResidueField R) p

variable (D : PData R p)

/-- The relation polynomial `T ^ (p ^ N) - b̃_j`. -/
noncomputable abbrev fN (N : ℕ) : D.pB → Polynomial R :=
  fun b => Polynomial.X ^ p ^ N - Polynomial.C (D.lift b)

/-- The `N`-th stage of the tower: `R[T_j : j ∈ Λ] ⧸ (T_j^{p^N} - b̃_j)`. -/
noncomputable abbrev AN (N : ℕ) : Type u :=
  MvPolynomial D.pB R ⧸ RFAux.qI (D.fN N)

noncomputable instance instCommRingAN (N : ℕ) : CommRing (D.AN N) := inferInstance

noncomputable instance instAlgebraAN (N : ℕ) : Algebra R (D.AN N) := inferInstance

/-- Reduced exponent vectors at level `N`. -/
abbrev Idx (N : ℕ) : Type u := {e : D.pB →₀ ℕ // ∀ a : D.pB, e a < p ^ N}

/-- The class of the reduced monomial with exponent vector `e`. -/
noncomputable abbrev mon (N : ℕ) (e : D.Idx N) : D.AN N :=
  Ideal.Quotient.mk (RFAux.qI (D.fN N)) (MvPolynomial.monomial e.1 1)

/-- The class of the variable `T_j = X_j` in the `N`-th stage. -/
noncomputable abbrev gen (N : ℕ) (b : D.pB) : D.AN N :=
  Ideal.Quotient.mk (RFAux.qI (D.fN N)) (MvPolynomial.X b)

/-- The structure map `R →+* AN D N`. -/
noncomputable abbrev toAN (N : ℕ) : R →+* D.AN N :=
  (Ideal.Quotient.mk (RFAux.qI (D.fN N))).comp MvPolynomial.C

variable {D}

lemma fN_apply (N : ℕ) (b : D.pB) :
    D.fN N b = Polynomial.X ^ p ^ N - Polynomial.C (D.lift b) := rfl

lemma gen_def (N : ℕ) (b : D.pB) :
    D.gen N b = Ideal.Quotient.mk (RFAux.qI (D.fN N)) (MvPolynomial.X b) := rfl

lemma toAN_apply (N : ℕ) (r : R) :
    D.toAN N r = Ideal.Quotient.mk (RFAux.qI (D.fN N)) (MvPolynomial.C r) := rfl

lemma toAN_eq_algebraMap (N : ℕ) (r : R) : D.toAN N r = algebraMap R (D.AN N) r := by
  rw [toAN_apply, ← MvPolynomial.algebraMap_eq]
  exact (Ideal.Quotient.mk_algebraMap R (RFAux.qI (D.fN N)) r).symm

/-- The evaluation of the relation polynomial `T^{p^N} - b̃_j` at the variable `X_j`. -/
lemma aeval_fN (N : ℕ) (b : D.pB) :
    (D.fN N b).aeval (MvPolynomial.X b : MvPolynomial D.pB R) =
      (MvPolynomial.X b : MvPolynomial D.pB R) ^ p ^ N - MvPolynomial.C (D.lift b) := by
  rw [fN_apply, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    MvPolynomial.algebraMap_eq]

/-- The defining relation of the `N`-th stage: `(T_j)^{p^N} = b̃_j`. -/
lemma gen_pow_eq (N : ℕ) (b : D.pB) :
    (D.gen N b) ^ p ^ N = algebraMap R (D.AN N) (D.lift b) := by
  rw [gen_def, ← map_pow, ← Ideal.Quotient.mk_algebraMap R (RFAux.qI (D.fN N)) (D.lift b),
    MvPolynomial.algebraMap_eq]
  refine Ideal.Quotient.eq.mpr ?_
  have hmem : (MvPolynomial.X b : MvPolynomial D.pB R) ^ p ^ N - MvPolynomial.C (D.lift b)
      ∈ RFAux.qI (D.fN N) :=
    Submodule.subset_span ⟨b, aeval_fN N b⟩
  simpa using hmem

lemma mon_eq (N : ℕ) (e : D.Idx N) :
    D.mon N e = Ideal.Quotient.mk (RFAux.qI (D.fN N)) (MvPolynomial.monomial e.1 1) := rfl

/-- The generators of the relation ideal of the `i`-th stage are killed by the transition map
`T_j ↦ T_j^{p^{j-i}}`. -/
lemma qI_le_ker_trans (i j : ℕ) (hij : i ≤ j) :
    RFAux.qI (D.fN i) ≤ RingHom.ker
      (MvPolynomial.eval₂Hom (D.toAN j) (fun b : D.pB => (D.gen j b) ^ p ^ (j - i))) := by
  rw [RFAux.qI]
  refine Ideal.span_le.mpr ?_
  intro a ha
  obtain ⟨b, hb⟩ := ha
  rw [← hb]
  show MvPolynomial.eval₂Hom (D.toAN j) (fun b : D.pB => (D.gen j b) ^ p ^ (j - i))
    ((Polynomial.aeval (MvPolynomial.X b)) (D.fN i b)) = 0
  rw [aeval_fN, map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
    toAN_apply]
  have h1 : ((Ideal.Quotient.mk (RFAux.qI (D.fN j))
        (MvPolynomial.X b : MvPolynomial D.pB R)) ^ p ^ (j - i)) ^ p ^ i =
      algebraMap R (D.AN j) (D.lift b) := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hij, gen_pow_eq]
  have h2 : Ideal.Quotient.mk (RFAux.qI (D.fN j)) (MvPolynomial.C (D.lift b) :
      MvPolynomial D.pB R) = algebraMap R (D.AN j) (D.lift b) := by
    rw [← MvPolynomial.algebraMap_eq]
    exact Ideal.Quotient.mk_algebraMap R (RFAux.qI (D.fN j)) (D.lift b)
  rw [h1, h2, sub_self]

/-- The transition map `AN D i →+* AN D j` (`i ≤ j`), sending `T_j` to `T_j^{p^{j-i}}`. -/
noncomputable abbrev trans (i j : ℕ) (hij : i ≤ j) : D.AN i →+* D.AN j :=
  Ideal.Quotient.lift (RFAux.qI (D.fN i))
    (MvPolynomial.eval₂Hom (D.toAN j)
      (fun b : D.pB => (D.gen j b) ^ p ^ (j - i)))
    (fun a ha => D.qI_le_ker_trans i j hij ha)

lemma trans_mk (i j : ℕ) (hij : i ≤ j) (x : MvPolynomial D.pB R) :
    D.trans i j hij (Ideal.Quotient.mk (RFAux.qI (D.fN i)) x) =
      MvPolynomial.eval₂Hom (D.toAN j)
        (fun b : D.pB => (D.gen j b) ^ p ^ (j - i)) x := by
  simpa using RingHom.congr_fun
    (Ideal.Quotient.lift_comp_mk (RFAux.qI (D.fN i))
      (MvPolynomial.eval₂Hom (D.toAN j) (fun b : D.pB => (D.gen j b) ^ p ^ (j - i)))
      (fun a ha => D.qI_le_ker_trans i j hij ha)) x

lemma trans_comp_mk (i j : ℕ) (hij : i ≤ j) :
    (D.trans i j hij).comp (Ideal.Quotient.mk (RFAux.qI (D.fN i))) =
      MvPolynomial.eval₂Hom (D.toAN j) (fun b : D.pB => (D.gen j b) ^ p ^ (j - i)) := by
  refine RingHom.ext (fun x => ?_)
  rw [RingHom.comp_apply]
  exact D.trans_mk i j hij x

lemma trans_gen (i j : ℕ) (hij : i ≤ j) (b : D.pB) :
    D.trans i j hij (D.gen i b) = (D.gen j b) ^ p ^ (j - i) := by
  rw [gen_def, trans_mk, MvPolynomial.eval₂Hom_X']

lemma trans_C (i j : ℕ) (hij : i ≤ j) (r : R) :
    D.trans i j hij (Ideal.Quotient.mk (RFAux.qI (D.fN i)) (MvPolynomial.C r)) =
      Ideal.Quotient.mk (RFAux.qI (D.fN j)) (MvPolynomial.C r) := by
  rw [trans_mk, MvPolynomial.eval₂Hom_C, toAN_apply]

lemma trans_toAN (i j : ℕ) (hij : i ≤ j) (r : R) :
    D.trans i j hij (D.toAN i r) = D.toAN j r := by
  rw [toAN_apply, toAN_apply]
  exact trans_C i j hij r

lemma trans_self (i : ℕ) : D.trans i i le_rfl = RingHom.id (D.AN i) := by
  refine Ideal.Quotient.ringHom_ext ?_
  rw [trans_comp_mk, RingHom.id_comp]
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun b => ?_)
  · rw [MvPolynomial.eval₂Hom_C, toAN_apply]
  · rw [MvPolynomial.eval₂Hom_X', gen_def]
    simp

lemma trans_trans (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (x : D.AN i) :
    D.trans j k hjk (D.trans i j hij x) = D.trans i k (hij.trans hjk) x := by
  have key : (D.trans j k hjk).comp (D.trans i j hij) = D.trans i k (hij.trans hjk) := by
    refine Ideal.Quotient.ringHom_ext ?_
    rw [RingHom.comp_assoc, trans_comp_mk]
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun b => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, toAN_apply,
        trans_C, trans_C]
    · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      show D.trans j k hjk ((D.gen j b) ^ p ^ (j - i)) =
        D.trans i k (hij.trans hjk) (D.gen i b)
      rw [map_pow, trans_gen, trans_gen, ← pow_mul, ← pow_add,
        show k - j + (j - i) = k - i by omega]
  exact RingHom.congr_fun key x

instance instDirectedSystem : DirectedSystem (fun N => D.AN N) (fun i j h => D.trans i j h) where
  map_self := fun i x => by
    rw [trans_self]
    rfl
  map_map := fun {k j i} hij hjk x => D.trans_trans i j k hij hjk x

/-- The colimit `S = colim_N AN D N` of the tower. -/
noncomputable abbrev S : Type u :=
  Ring.DirectLimit (fun N => D.AN N) (fun i j h => D.trans i j h)

noncomputable instance instCommRingS : CommRing D.S := inferInstance

/-- The canonical map from a stage into the colimit. -/
noncomputable abbrev incl (N : ℕ) : D.AN N →+* D.S :=
  Ring.DirectLimit.of (fun N => D.AN N) (fun i j h => D.trans i j h) N

lemma incl_trans (i j : ℕ) (hij : i ≤ j) (x : D.AN i) :
    D.incl j (D.trans i j hij x) = D.incl i x :=
  Ring.DirectLimit.of_f hij x

/-- The structure map `R →+* S`, through the zeroth stage. -/
noncomputable abbrev phi : R →+* D.S := (D.incl 0).comp (D.toAN 0)

lemma phi_apply (r : R) : D.phi r = D.incl 0 (D.toAN 0 r) := rfl

lemma incl_toAN (N : ℕ) (r : R) : D.incl N (D.toAN N r) = D.phi r := by
  show D.incl N (D.toAN N r) = D.incl 0 (D.toAN 0 r)
  rw [← incl_trans 0 N (Nat.zero_le N) (D.toAN 0 r), ← trans_toAN 0 N (Nat.zero_le N) r]

lemma incl_eq_phi_algebraMap (N : ℕ) (r : R) :
    D.incl N (algebraMap R (D.AN N) r) = D.phi r := by
  rw [← toAN_eq_algebraMap]
  exact incl_toAN N r

/-! ### The maps onto the perfect closure of the residue field -/

/-- A `p ^ N`-th root in the perfect closure. -/
lemma pc_mk_pow (N : ℕ) (x : IsLocalRing.ResidueField R) :
    (PerfectClosure.mk (IsLocalRing.ResidueField R) p (N, x)) ^ p ^ N =
      PerfectClosure.of (IsLocalRing.ResidueField R) p x := by
  induction N with
  | zero => rw [PerfectClosure.of_apply (IsLocalRing.ResidueField R) p x]; simp
  | succ n ih =>
    rw [pow_succ', pow_mul, PerfectClosure.mk_pow, PerfectClosure.mk_succ_pow]
    exact ih

/-- `x ^ (p ^ -(i+d))` raised to the `p ^ d`-th power is `x ^ (p ^ -i)`. -/
lemma pc_mk_pow_add (i d : ℕ) (x : IsLocalRing.ResidueField R) :
    (PerfectClosure.mk (IsLocalRing.ResidueField R) p (i + d, x)) ^ p ^ d =
      PerfectClosure.mk (IsLocalRing.ResidueField R) p (i, x) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, pow_succ', pow_mul, PerfectClosure.mk_pow, PerfectClosure.mk_succ_pow]
    exact ih

/-- The generators of the relation ideal are killed by the map onto the perfect closure. -/
lemma qI_le_ker_tauN (N : ℕ) :
    RFAux.qI (D.fN N) ≤ RingHom.ker
      (MvPolynomial.eval₂Hom
        ((PerfectClosure.of (IsLocalRing.ResidueField R) p).comp (IsLocalRing.residue R))
        (fun b : D.pB =>
          PerfectClosure.mk (IsLocalRing.ResidueField R) p (N, (b : IsLocalRing.ResidueField R)))) := by
  rw [RFAux.qI]
  refine Ideal.span_le.mpr ?_
  intro a ha
  obtain ⟨b, hb⟩ := ha
  rw [← hb]
  show MvPolynomial.eval₂Hom _ (fun b : D.pB =>
      PerfectClosure.mk (IsLocalRing.ResidueField R) p (N, (b : IsLocalRing.ResidueField R)))
    ((Polynomial.aeval (MvPolynomial.X b)) (D.fN N b)) = 0
  have h1 : (PerfectClosure.mk (IsLocalRing.ResidueField R) p
        (N, (b : IsLocalRing.ResidueField R))) ^ p ^ N =
      (PerfectClosure.of (IsLocalRing.ResidueField R) p) (b : IsLocalRing.ResidueField R) :=
    pc_mk_pow N (b : IsLocalRing.ResidueField R)
  rw [aeval_fN, map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, h1,
    RingHom.comp_apply, D.lift_spec, sub_self]

/-- The map `AN D N →+* PC` sending `T_j` to the `p^N`-th root of `j`. -/
noncomputable abbrev tauN (N : ℕ) : D.AN N →+* D.PC :=
  Ideal.Quotient.lift (RFAux.qI (D.fN N))
    (MvPolynomial.eval₂Hom
      ((PerfectClosure.of (IsLocalRing.ResidueField R) p).comp (IsLocalRing.residue R))
      (fun b : D.pB =>
        PerfectClosure.mk (IsLocalRing.ResidueField R) p (N, (b : IsLocalRing.ResidueField R))))
    (fun a ha => D.qI_le_ker_tauN N ha)

lemma tauN_mk (N : ℕ) (x : MvPolynomial D.pB R) :
    D.tauN N (Ideal.Quotient.mk (RFAux.qI (D.fN N)) x) =
      MvPolynomial.eval₂Hom
        ((PerfectClosure.of (IsLocalRing.ResidueField R) p).comp (IsLocalRing.residue R))
        (fun b : D.pB =>
          PerfectClosure.mk (IsLocalRing.ResidueField R) p (N, (b : IsLocalRing.ResidueField R))) x := by
  simpa using RingHom.congr_fun
    (Ideal.Quotient.lift_comp_mk (RFAux.qI (D.fN N))
      (MvPolynomial.eval₂Hom
        ((PerfectClosure.of (IsLocalRing.ResidueField R) p).comp (IsLocalRing.residue R))
        (fun b : D.pB =>
          PerfectClosure.mk (IsLocalRing.ResidueField R) p (N, (b : IsLocalRing.ResidueField R))))
      (fun a ha => D.qI_le_ker_tauN N ha)) x

lemma tauN_gen (N : ℕ) (b : D.pB) :
    D.tauN N (D.gen N b) =
      PerfectClosure.mk (IsLocalRing.ResidueField R) p (N, (b : IsLocalRing.ResidueField R)) := by
  rw [gen_def, tauN_mk, MvPolynomial.eval₂Hom_X']

lemma tauN_toAN (N : ℕ) (r : R) :
    D.tauN N (D.toAN N r) = (PerfectClosure.of (IsLocalRing.ResidueField R) p)
      (IsLocalRing.residue R r) := by
  rw [toAN_apply, tauN_mk, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]

lemma tauN_trans (i j : ℕ) (hij : i ≤ j) (x : D.AN i) :
    D.tauN j (D.trans i j hij x) = D.tauN i x := by
  have key : (D.tauN j).comp (D.trans i j hij) = D.tauN i := by
    refine Ideal.Quotient.ringHom_ext ?_
    rw [RingHom.comp_assoc, trans_comp_mk]
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun b => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, toAN_apply, tauN_mk]
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', tauN_gen, map_pow]
      rw [show PerfectClosure.mk (IsLocalRing.ResidueField R) p (j, (b : IsLocalRing.ResidueField R))
          = PerfectClosure.mk (IsLocalRing.ResidueField R) p
              (i + (j - i), (b : IsLocalRing.ResidueField R))
          from by rw [Nat.add_sub_of_le hij]]
      exact pc_mk_pow_add i (j - i) (b : IsLocalRing.ResidueField R)
  exact RingHom.congr_fun key x

/-- The map `S →+* PC` from the colimit. -/
noncomputable abbrev psi : D.S →+* D.PC :=
  Ring.DirectLimit.lift (fun N => D.AN N) (fun i j h => D.trans i j h) D.PC
    (fun N => D.tauN N)
    (fun i j hij x => D.tauN_trans i j hij x)

lemma psi_incl (N : ℕ) (x : D.AN N) : D.psi (D.incl N x) = D.tauN N x := by
  rw [psi, incl, Ring.DirectLimit.lift_of]

lemma psi_comp_phi (r : R) :
    D.psi (D.phi r) = (PerfectClosure.of (IsLocalRing.ResidueField R) p)
      (IsLocalRing.residue R r) := by
  rw [phi, RingHom.comp_apply, psi_incl, tauN_toAN]

end PData


/-!
## Roadmap: the lemmas needed for `exists_flat_local_perfect_residue`

Given `D : PData R p` (so `k = IsLocalRing.ResidueField R` has characteristic `p`, `Λ = D.pB` is a
`p`-basis of `k` over `k ^ p` exhibited by the monomial basis `D.basis` (`D.basis_apply`), and
`D.lift : Λ → R` lifts the residue map), the colimit `S = D.S` of the tower `AN D N` has the
following properties.

1. **Spanning of a stage.** Every element of `AN D N` is an `R`-linear combination of the classes
   `D.mon N e` of the reduced monomials (`e : Λ →₀ ℕ` with entries `< p ^ N`). Proof: for a monomial
   `X ^ m` write `m = p ^ N • q + s` componentwise; then `X ^ m = (∏_j b̃_j ^ (q j)) · X ^ s` modulo
   the relations, and conclude by `Submodule.span_induction` on the ideal `RFAux.qI (D.fN N)` (the
   `RFAux.redLin` retraction of `Submission.Work.DSG4b.rootLocal_flat` gives the same statement).

2. **The fibre.** `RingHom.ker (D.tauN N) = Ideal.map (algebraMap R (D.AN N)) 𝔪`. For `⊆`: write
   `a = Σ_e r_e • D.mon N e` as in 1. Since `D.tauN N (D.mon N e) = ∏_j mk (N, j) ^ (e j)` (the
   `p ^ N`-th root of the monomial), the relation `D.tauN N a = 0` reads
   `Σ_e (D.tauN N (D.mon N e)) · residue (r_e) = 0` in `PC`; raising to the `p ^ N`-th power (in
   characteristic `p`, using `PerfectClosure.mk_pow` and `pc_mk_pow`) turns it into
   `Σ_e (residue r_e) ^ (p ^ N) · mon_e(Λ) = 0` in `k`. The monomials of exponent `< p ^ N` form a
   `k ^ (p ^ N)`-basis of `k` (`Work.DSG4b.pBasis.pBasis_pow_basis` applied to `D.basis`, or
   `Work.DSG4b.gonfPerfect.pbPow.pBasisPowBasis`), so every `residue r_e` vanishes.

3. **Surjectivity of `psi`.** Every element of `PC = PerfectClosure k p` is some `mk (m, x)`, and `x`
   is a `k ^ (p ^ m)`-linear combination of the monomials of exponent `< p ^ m` (same input as in 2).
   Then `mk (m, x)` is the image of an element of `AN D m`: raise the corresponding expression to the
   `p ^ m`-th power and use that the `p ^ m`-th power map of the perfect field `PC` is injective.

4. **Flatness.** `D.phi.Flat`: use the equational criterion
   (`Module.Flat.iff_forall_isTrivialRelation`). A relation in `S` involves finitely many elements,
   all in the image of one stage `AN D N` (`Ring.DirectLimit.exists_of`); the relation then already
   holds in a stage `AN D M` (`Ring.DirectLimit.of.zero_exact`), where it is trivial because
   `AN D M` is free over `R` (`RFAux.flat_quotient_monic`), and it can be pushed back to `S`.

5. **Integrality.** `D.phi.IsIntegral`: each `T_j` is a root of the monic polynomial
   `T ^ (p ^ N) - b̃_j` (`D.gen_pow_eq`), so `AN D N` is generated over `R` by integral elements and
   is therefore integral over `R`; integrality passes to the colimit.

6. **Every maximal ideal of `S` lies over `𝔪`.** This follows from 5 via
   `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`; since `psi` is surjective with kernel
   `𝔪 · S` and `PC` is a field, `𝔪 · S` is maximal, hence the unique maximal ideal of `S`.
-/

end Work.DSG4b.gonfPerfect

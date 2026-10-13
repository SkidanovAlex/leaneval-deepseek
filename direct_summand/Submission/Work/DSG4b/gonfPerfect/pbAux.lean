import Mathlib

/-!
# `pbAux` — a self-contained copy of the `p`-basis theory

This file is a verbatim copy (with the namespace renamed) of the files
`Submission/Work/DSG4b/pBasis/{Basic,Span,Chain,Field,Assembly}.lean` of this workspace, made so
that the results are available *without* importing `Submission.Work.DSG4b.pBasis.Basic` (whose
`Work.DSG4b.pBasis.Idx` clashes by name with the one defined by
`Submission.Work.DSG4b.pBasis.pBasis_pow_basis`, which the proof of
`exists_flat_local_perfect_residue` also needs).
-/



/-!
# `p`-bases: vocabulary

Let `L` be a field of characteristic a prime `p`, and let `L ^ p = (frobenius L p).fieldRange` be
the subfield of `p`-th powers.  This file fixes the vocabulary used to discuss `p`-bases of `L`
over `L ^ p`:

* `mon e` is the monomial `∏ a ^ (e a)` attached to an exponent vector `e : L →₀ ℕ`;
* `Idx L p S` is the type of exponent vectors supported in `S` with all entries `< p`;
* `pMon L p S` is the resulting family of monomials;
* `IsPIndep L p S` says that this family is linearly independent over `L ^ p`;
* `pSpan L p S` is the `L ^ p`-span of the monomials over `S`, i.e. the subspace that a `p`-basis
  candidate `S` is supposed to span.

The main result, `Work.DSG4b.gonfPerfect.pbAux.exists_pBasis`, is that `L` always admits a `p`-basis.
-/

namespace Work.DSG4b.gonfPerfect.pbAux

universe u

section Monomial

variable {L : Type*}

/-- The monomial `∏ a ^ (e a)` attached to an exponent vector `e : L →₀ ℕ`. -/
def mon [CommMonoid L] (e : L →₀ ℕ) : L := e.prod fun a k => a ^ k

@[simp]
theorem mon_zero [CommMonoid L] : mon (0 : L →₀ ℕ) = 1 := Finsupp.prod_zero_index

theorem mon_add [CommMonoid L] (e f : L →₀ ℕ) : mon (e + f) = mon e * mon f :=
  Finsupp.prod_add_index' (fun _ => by simp) fun _ _ _ => by rw [pow_add]

@[simp]
theorem mon_single [CommMonoid L] (a : L) (k : ℕ) : mon (Finsupp.single a k) = a ^ k :=
  Finsupp.prod_single_index (by simp)

end Monomial

variable (L : Type u) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

/-- The subfield `L ^ p ⊆ L` of `p`-th powers, i.e. the range of the Frobenius. -/
abbrev pthPowerField : Subfield L := (frobenius L p).fieldRange

/-- Exponent vectors supported in `S` whose entries are all `< p`. -/
abbrev Idx (S : Set L) : Type u := {e : L →₀ ℕ // (e.support : Set L) ⊆ S ∧ ∀ a, e a < p}

/-- The family of monomials `∏ a ^ (e a)` with exponents `< p` over a set `S ⊆ L`. -/
abbrev pMon (S : Set L) : Idx L p S → L := fun e => mon e.1

/-- `S` is `p`-independent if the monomials with exponents `< p` over `S` are linearly
independent over `L ^ p`. -/
abbrev IsPIndep (S : Set L) : Prop :=
  LinearIndependent (pthPowerField L p) (pMon L p S)

/-- The `L ^ p`-span of the monomials with exponents `< p` over `S`; a `p`-basis candidate `S`
spans `L` exactly when this is `⊤`. -/
abbrev pSpan (S : Set L) : Submodule (pthPowerField L p) L :=
  Submodule.span (pthPowerField L p) (Set.range (pMon L p S))

variable {L p}

theorem mem_pSpan_of_mem (S : Set L) {e : L →₀ ℕ}
    (he : (e.support : Set L) ⊆ S) (hp : ∀ a, e a < p) : mon e ∈ pSpan L p S :=
  Submodule.subset_span ⟨⟨e, he, hp⟩, rfl⟩

theorem subset_pSpan (S : Set L) : S ⊆ (pSpan L p S : Set L) := by
  intro a ha
  have hp1 : 1 < p := Nat.Prime.one_lt (Fact.out)
  have hpp : 0 < p := Nat.Prime.pos (Fact.out)
  have h1 : ((Finsupp.single a 1).support : Set L) ⊆ S := by
    intro y hy
    have hya : y = a := by
      simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hy
      by_cases h : y = a
      · exact h
      · simp [h] at hy
    rwa [hya]
  have h2 : ∀ b, Finsupp.single a 1 b < p := by
    intro b
    by_cases hb : b = a
    · subst hb
      rw [Finsupp.single_eq_same]
      exact hp1
    · rw [Finsupp.single_eq_of_ne hb]
      exact hpp
  have h3 := mem_pSpan_of_mem (p := p) S h1 h2
  simpa [mon_single] using h3

end Work.DSG4b.gonfPerfect.pbAux




/-!
# The subfield `pSpan` of `p`-th-power monomial combinations

For a field `L` of characteristic a prime `p` and a subset `S ⊆ L`, the `L^p`-submodule
`pSpan L p S` spanned by the monomials `∏ a ^ (e a)` (`e` supported in `S`, all entries `< p`)
is in fact a *subfield* of `L`: it is closed under multiplication (reduce exponents mod `p` using
`a ^ p ∈ L ^ p`) and under inversion (`b ^ p ∈ L ^ p` for every `b`).

This is the key structural fact behind the existence of `p`-bases: a maximal `p`-independent set
`Λ` must satisfy `pSpan L p Λ = ⊤`, since an element outside `pSpan L p Λ` would either be
adjoinable or already lie in the (field!) `pSpan`.
-/

namespace Work.DSG4b.gonfPerfect.pbAux

variable {L : Type*}

/-- Splitting the exponents of a monomial into residues and quotients modulo `p`:
`∏ a ^ (u a) = (∏ a ^ (u a % p)) * (∏ a ^ (u a / p)) ^ p`. -/
theorem mon_eq_mon_mod_mul_mon_div_pow [CommMonoid L] (p : ℕ) (u : L →₀ ℕ) :
    mon u = mon (u.mapRange (fun k => k % p) (Nat.zero_mod p)) *
      (mon (u.mapRange (fun k => k / p) (Nat.zero_div p))) ^ p := by
  have hmod : ∀ a : L, a ^ (u a) = a ^ (u a % p) * (a ^ (u a / p)) ^ p := by
    intro a
    rw [← pow_mul, ← pow_add]
    congr 1
    rw [mul_comm, add_comm]
    exact (Nat.div_add_mod (u a) p).symm
  have hpow : (u.prod fun a k => a ^ (k / p)) ^ p =
      u.prod fun a k => (a ^ (k / p)) ^ p := by
    rw [Finsupp.prod, Finsupp.prod, Finset.prod_pow]
  rw [mon, mon, mon,
    Finsupp.prod_mapRange_index (h := fun a k => a ^ k) (fun a => pow_zero a),
    Finsupp.prod_mapRange_index (h := fun a k => a ^ k) (fun a => pow_zero a),
    hpow, ← Finsupp.prod_mul]
  exact Finsupp.prod_congr fun a _ => hmod a

variable (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

theorem pow_mem_pthPowerField (a : L) : a ^ p ∈ pthPowerField L p := by
  rw [RingHom.mem_fieldRange]
  exact ⟨a, frobenius_def p a⟩

/-- Every monomial whose exponents are supported in `S` lies in `pSpan L p S` (no bound on the
exponents). -/
theorem mon_mem_pSpan_of_support_subset (S : Set L) {u : L →₀ ℕ}
    (hu : (u.support : Set L) ⊆ S) : mon u ∈ pSpan L p S := by
  have hp : 0 < p := Nat.Prime.pos (Fact.out)
  rw [mon_eq_mon_mod_mul_mon_div_pow]
  have h1 : mon (u.mapRange (fun k => k % p) (Nat.zero_mod p)) ∈ pSpan L p S := by
    refine mem_pSpan_of_mem S ?_ ?_
    · intro x hx
      exact hu (Finsupp.support_mapRange hx)
    · intro a
      rw [Finsupp.mapRange_apply]
      exact Nat.mod_lt _ hp
  have hcoe : (algebraMap (pthPowerField L p) L)
      ⟨(mon (u.mapRange (fun k => k / p) (Nat.zero_div p))) ^ p,
        pow_mem_pthPowerField L p _⟩
      = (mon (u.mapRange (fun k => k / p) (Nat.zero_div p))) ^ p := rfl
  have hscal := Submodule.smul_mem (pSpan L p S)
    (⟨(mon (u.mapRange (fun k => k / p) (Nat.zero_div p))) ^ p,
      pow_mem_pthPowerField L p _⟩ : pthPowerField L p) h1
  simpa [Algebra.smul_def, mul_comm, hcoe] using hscal

/-- The image of `L ^ p` in `L` lies in `pSpan L p S`. -/
theorem pSpan_algebraMap_mem (S : Set L) (c : pthPowerField L p) :
    (c : L) ∈ pSpan L p S := by
  have h1 : mon (0 : L →₀ ℕ) ∈ pSpan L p S :=
    mem_pSpan_of_mem S (by simp) (fun a => Nat.Prime.pos (Fact.out))
  have h2 : c • (mon (0 : L →₀ ℕ)) ∈ pSpan L p S := Submodule.smul_mem _ c h1
  have h3 : c • (mon (0 : L →₀ ℕ)) = (c : L) := by
    simp only [mon_zero, Algebra.smul_def, mul_one, Subfield.algebraMap_ofSubfield,
      Subfield.subtype_apply]
  rwa [h3] at h2

theorem pSpan_one_mem (S : Set L) : (1 : L) ∈ pSpan L p S := by
  have h1 : mon (0 : L →₀ ℕ) ∈ pSpan L p S :=
    mem_pSpan_of_mem S (by simp) (fun a => Nat.Prime.pos (Fact.out))
  simpa using h1

theorem pSpan_zero_mem (S : Set L) : (0 : L) ∈ pSpan L p S := Submodule.zero_mem _

theorem pSpan_add_mem (S : Set L) {a b : L} (ha : a ∈ pSpan L p S) (hb : b ∈ pSpan L p S) :
    a + b ∈ pSpan L p S := Submodule.add_mem _ ha hb

theorem pSpan_neg_mem (S : Set L) {a : L} (ha : a ∈ pSpan L p S) : -a ∈ pSpan L p S :=
  Submodule.neg_mem _ ha

/-- `pSpan L p S` is closed under multiplication by any monomial supported in `S`. -/
theorem pSpan_mul_mon_mem (S : Set L) {u : L →₀ ℕ} (hu : (u.support : Set L) ⊆ S)
    {a : L} (ha : a ∈ pSpan L p S) : a * mon u ∈ pSpan L p S := by
  induction ha using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨w, rfl⟩ := hv
      show mon w.1 * mon u ∈ pSpan L p S
      rw [← mon_add]
      refine mon_mem_pSpan_of_support_subset L p S ?_
      intro x hx
      have hx' : (w.1 + u) x ≠ 0 := by
        simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hx
      by_cases hwx : w.1 x = 0
      · have hux : u x ≠ 0 := by
          intro h0
          exact hx' (by rw [Finsupp.add_apply, hwx, h0, add_zero])
        exact hu (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hux)
      · exact w.2.1 (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hwx)
  | zero =>
      rw [zero_mul]
      exact pSpan_zero_mem L p S
  | add x y _ _ hx hy =>
      rw [add_mul]
      exact pSpan_add_mem L p S hx hy
  | smul c x _ hx =>
      have hc : (c • x) * mon u = c • (x * mon u) := by
        rw [Algebra.smul_def, Algebra.smul_def]; ring
      rw [hc]
      exact Submodule.smul_mem _ c hx

/-- `pSpan L p S` is closed under multiplication. -/
theorem pSpan_mul_mem (S : Set L) {a b : L} (ha : a ∈ pSpan L p S)
    (hb : b ∈ pSpan L p S) : a * b ∈ pSpan L p S := by
  induction hb using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨w, rfl⟩ := hv
      exact pSpan_mul_mon_mem L p S w.2.1 ha
  | zero =>
      rw [mul_zero]
      exact pSpan_zero_mem L p S
  | add x y _ _ hx hy =>
      rw [mul_add]
      exact pSpan_add_mem L p S hx hy
  | smul c x _ hx =>
      have hc : a * (c • x) = c • (a * x) := by
        rw [Algebra.smul_def, Algebra.smul_def]; ring
      rw [hc]
      exact Submodule.smul_mem _ c hx

theorem pSpan_pow_mem (S : Set L) {a : L} (ha : a ∈ pSpan L p S) (n : ℕ) :
    a ^ n ∈ pSpan L p S := by
  induction n with
  | zero => simpa using pSpan_one_mem L p S
  | succ n ih =>
      rw [pow_succ]
      exact pSpan_mul_mem L p S ih ha

/-- `pSpan L p S` is closed under inversion. -/
theorem pSpan_inv_mem (S : Set L) {a : L} (ha : a ∈ pSpan L p S) : a⁻¹ ∈ pSpan L p S := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [inv_zero]
    exact pSpan_zero_mem L p S
  · have hp1 : 1 ≤ p := Nat.Prime.one_le (Fact.out)
    have h1 : a ^ (p - 1) ∈ pSpan L p S := pSpan_pow_mem L p S ha (p - 1)
    have h2 : (a ^ p)⁻¹ ∈ pSpan L p S :=
      pSpan_algebraMap_mem L p S
        ⟨(a ^ p)⁻¹, (pthPowerField L p).inv_mem (pow_mem_pthPowerField L p a)⟩
    have h3 := pSpan_mul_mem L p S h1 h2
    have hsplit : a ^ p = a ^ (p - 1) * a := by
      rw [← pow_succ, Nat.sub_add_cancel hp1]
    have : a ^ (p - 1) * (a ^ p)⁻¹ = a⁻¹ := by
      rw [hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha0), one_mul]
    rwa [this] at h3

/-- The `L ^ p`-span of the monomials over `S`, as a subfield of `L`. -/
def pSubfield (S : Set L) : Subfield L where
  carrier := (pSpan L p S : Set L)
  zero_mem' := pSpan_zero_mem L p S
  one_mem' := pSpan_one_mem L p S
  add_mem' := fun ha hb => pSpan_add_mem L p S ha hb
  neg_mem' := fun ha => pSpan_neg_mem L p S ha
  mul_mem' := fun ha hb => pSpan_mul_mem L p S ha hb
  inv_mem' := fun _ hx => pSpan_inv_mem L p S hx

@[simp]
theorem coe_pSubfield (S : Set L) : (pSubfield L p S : Set L) = (pSpan L p S : Set L) := rfl

end Work.DSG4b.gonfPerfect.pbAux




/-!
# `IsPIndep` is of finite character

The family of `p`-independent subsets of `L` is closed under unions of chains: a linear dependence
only involves finitely many monomials, each of which involves only finitely many elements of `L`,
and a chain of sets contains a member carrying all of them.  This is what makes Zorn's lemma
applicable in the proof of `Work.DSG4b.gonfPerfect.pbAux.exists_pBasis`.
-/

namespace Work.DSG4b.gonfPerfect.pbAux

variable (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

/-- If a relation among monomials over `S` has all its supports inside a `p`-independent set `a₀`,
then all its coefficients vanish. -/
theorem coeff_eq_zero_of_cover (S a₀ : Set L) (hind : IsPIndep L p a₀)
    (s : Finset (Idx L p S)) (g : Idx L p S → pthPowerField L p)
    (hsum : ∑ v ∈ s, g v • pMon L p S v = 0)
    (hcover : ∀ v ∈ s, (v.1.support : Set L) ⊆ a₀) :
    ∀ u ∈ s, g u = 0 := by
  classical
  let ψ : {v : Idx L p S // v ∈ s} → Idx L p a₀ :=
    fun v => ⟨v.1.1, hcover v.1 v.2, v.1.2.2⟩
  have hinj : Function.Injective ψ := by
    intro a b hab
    have h1 : a.1.1 = b.1.1 := congrArg (fun w : Idx L p a₀ => w.1) hab
    exact Subtype.ext (Subtype.ext h1)
  have hli : LinearIndependent (pthPowerField L p)
      (fun v : {v : Idx L p S // v ∈ s} => pMon L p a₀ (ψ v)) :=
    hind.comp ψ hinj
  rw [linearIndependent_iff'] at hli
  have hsum' : (∑ v : {v : Idx L p S // v ∈ s}, g v.1 • pMon L p a₀ (ψ v)) = 0 := by
    have h1 : (∑ v : {v : Idx L p S // v ∈ s}, g v.1 • pMon L p a₀ (ψ v)) =
        ∑ v : {v : Idx L p S // v ∈ s}, g v.1 • pMon L p S v.1 :=
      Finset.sum_congr rfl fun v _ => by simp only [pMon, ψ]
    have h2 : (∑ v : {v : Idx L p S // v ∈ s}, g v.1 • pMon L p S v.1) =
        ∑ v ∈ s, g v • pMon L p S v :=
      Finset.sum_attach s fun w : Idx L p S => g w • pMon L p S w
    rw [h1, h2]
    exact hsum
  intro u hu
  exact hli Finset.univ (fun v => g v.1) hsum' ⟨u, hu⟩ (Finset.mem_univ _)

/-- The empty set is `p`-independent. -/
theorem isPIndep_empty : IsPIndep L p (∅ : Set L) := by
  classical
  rw [IsPIndep, linearIndependent_iff']
  intro s g hsum u hu
  have hzero : ∀ v : Idx L p (∅ : Set L), v.1 = 0 := by
    intro v
    ext a
    by_contra h
    exact v.2.1 (by
      simpa only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.zero_apply] using h)
  have hsu : s ⊆ {u} := by
    intro v _
    rw [Finset.mem_singleton]
    exact Subtype.ext (by rw [hzero v, hzero u])
  have h1 : (∑ v ∈ s, g v • pMon L p (∅ : Set L) v) =
      g u • pMon L p (∅ : Set L) u := by
    rw [Finset.sum_subset hsu]
    · rw [Finset.sum_singleton]
    · intro w hw hw'
      exfalso
      rw [Finset.mem_singleton] at hw
      subst hw
      exact absurd hu hw'
  rw [h1] at hsum
  have hmon : pMon L p (∅ : Set L) u = 1 := by
    simp only [pMon, hzero u, mon_zero]
  rw [hmon, Algebra.smul_def, mul_one] at hsum
  exact Subtype.ext (by simpa using hsum)

/-- A finite set of elements lying in the union of a chain of sets is contained in a single member
of the chain. -/
theorem exists_mem_chain_subset_of_finset {α : Type*} (c : Set (Set α))
    (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty) (t : Finset α) (ht : (t : Set α) ⊆ ⋃₀ c) :
    ∃ S ∈ c, (t : Set α) ⊆ S := by
  classical
  revert ht
  induction t using Finset.induction with
  | empty =>
      intro _
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, by simp⟩
  | insert x t hxt ih =>
      intro ht
      have ht' : (t : Set α) ⊆ ⋃₀ c := fun y hy => ht (by simp [hy])
      obtain ⟨St, hStc, hSt⟩ := ih ht'
      have hx : x ∈ ⋃₀ c := ht (by simp)
      obtain ⟨Sx, hSxc, hxSx⟩ := hx
      rcases hc.total hStc hSxc with hle | hle
      · refine ⟨Sx, hSxc, fun y hy => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact hxSx
        · exact hle (hSt hy')
      · refine ⟨St, hStc, fun y hy => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact hle hxSx
        · exact hSt hy'

/-- The supports of finitely many monomials over `⋃₀ c` all lie in a single member of the
chain `c`. -/
theorem exists_mem_chain_covering (c : Set (Set L)) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (s : Finset (Idx L p (⋃₀ c))) :
    ∃ S ∈ c, ∀ v ∈ s, (v.1.support : Set L) ⊆ S := by
  classical
  induction s using Finset.induction with
  | empty =>
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, by simp⟩
  | insert v s _ ih =>
      obtain ⟨S₁, hS₁c, h₁⟩ := ih
      obtain ⟨S₂, hS₂c, h₂⟩ := exists_mem_chain_subset_of_finset c hc hne v.1.support
        (fun y hy => v.2.1 hy)
      rcases hc.total hS₁c hS₂c with hle | hle
      · refine ⟨S₂, hS₂c, fun w hw => ?_⟩
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact h₂
        · exact (h₁ w hw').trans hle
      · refine ⟨S₁, hS₁c, fun w hw => ?_⟩
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact h₂.trans hle
        · exact h₁ w hw'

/-- `IsPIndep` is preserved by unions of chains. -/
theorem isPIndep_sUnion_of_isChain (c : Set (Set L)) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (h : ∀ S ∈ c, IsPIndep L p S) : IsPIndep L p (⋃₀ c) := by
  rw [IsPIndep, linearIndependent_iff']
  intro s g hsum u hu
  obtain ⟨a₀, ha₀c, hcover⟩ := exists_mem_chain_covering L p c hc hne s
  exact coeff_eq_zero_of_cover L p (⋃₀ c) a₀ (h a₀ ha₀c) s g hsum hcover u hu

end Work.DSG4b.gonfPerfect.pbAux




/-!
# A `p`-undefined relation forces membership

Let `F ⊆ L` be a subfield of a field `L` of characteristic a prime `p`, and let `x ∈ L` satisfy
`x ^ p ∈ F`.  If `x` satisfies a *nontrivial* polynomial relation `∑_{k<p} A_k x^k = 0` with all
`A_k ∈ F`, then already `x ∈ F`.

The proof does not factor the minimal polynomial: since `x ^ p ∈ F`, the minimal polynomial of `x`
over `F` has separable degree one, so by `minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow` it maps
to `(X - x) ^ (p ^ n)`.  Comparing the degrees with the degree bound `< p` coming from the
relation forces `n = 0`, hence the minimal polynomial maps to `X - x` and its constant coefficient
exhibits `x` as an element of `F`.

This is the "purely inseparable degree" step in the proof of
`Work.DSG4b.gonfPerfect.pbAux.exists_pBasis`.
-/

namespace Work.DSG4b.gonfPerfect.pbAux

/-- **A nontrivial relation of degree `< p` over `F` forces `x ∈ F`.** -/
theorem mem_of_relation (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (F : Subfield L) (x : L) (hx : x ^ p ∈ F) (A : Fin p → L) (hA : ∀ k, A k ∈ F)
    (hne : ∃ k, A k ≠ 0) (h : (∑ k : Fin p, A k * x ^ (k : ℕ)) = 0) : x ∈ F := by
  classical
  -- the polynomial `g = ∑ k A k · X ^ k`
  set g : Polynomial F := ∑ k : Fin p, Polynomial.monomial (k : ℕ) ⟨A k, hA k⟩ with hg
  have hC : ∀ k : Fin p, (algebraMap F L) ⟨A k, hA k⟩ = A k := fun k => rfl
  have haev : Polynomial.aeval x g = 0 := by
    rw [hg, map_sum]
    simp only [Polynomial.aeval_monomial, hC]
    exact h
  have hgne : g ≠ 0 := by
    intro h0
    obtain ⟨j, hj⟩ := hne
    have h1 : g.coeff (j : ℕ) = 0 := by rw [h0, Polynomial.coeff_zero]
    have h2 : g.coeff (j : ℕ) = ⟨A j, hA j⟩ := by
      rw [hg, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single j]
      · simp only [Polynomial.coeff_monomial]
        split_ifs <;> rfl
      · intro b _ hb
        simp only [Polynomial.coeff_monomial]
        split_ifs with hcontra
        · exact absurd (Fin.ext hcontra) hb
        · rfl
      · intro hj'
        exact absurd (Finset.mem_univ j) hj'
    rw [h2] at h1
    exact hj (by simpa using congr_arg Subtype.val h1)
  have hdeg : g.natDegree < p := by
    have h1 : g.natDegree ≤ p - 1 := by
      rw [hg]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
      intro k _
      rw [Polynomial.natDegree_monomial]
      split
      · exact Nat.zero_le _
      · exact Nat.le_sub_one_of_lt k.2
    exact lt_of_le_of_lt h1 (Nat.sub_lt (Nat.Prime.pos (Fact.out)) Nat.one_pos)
  have hlt : (minpoly F x).natDegree < p :=
    lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd (minpoly.dvd F x haev) hgne) hdeg
  have hsep : (minpoly F x).natSepDegree = 1 := by
    rw [minpoly.natSepDegree_eq_one_iff_pow_mem p (x := x)]
    refine ⟨1, ⟨⟨x ^ p, hx⟩, ?_⟩⟩
    rw [pow_one, Subfield.algebraMap_ofSubfield, Subfield.subtype_apply]
  obtain ⟨n, hn⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow p (x := x)).mp hsep
  have hnat : (minpoly F x).natDegree = p ^ n := by
    rw [← Polynomial.natDegree_map_eq_of_injective (algebraMap F L).injective (minpoly F x), hn,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hn0 : n = 0 := by
    by_contra hn0
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have h2 : p ^ 1 ≤ p ^ n := pow_le_pow_right₀ (Nat.Prime.one_le (Fact.out)) h1
    rw [pow_one] at h2
    have h3 : p ^ n < p := by rw [← hnat]; exact hlt
    exact absurd h3 (not_lt.mpr h2)
  rw [hn0, pow_zero, pow_one] at hn
  have hcoeff : (algebraMap F L) ((minpoly F x).coeff 0) = -x := by
    have h1 := congr_arg (fun q : Polynomial L => q.coeff 0) hn
    rw [Polynomial.coeff_map] at h1
    simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub] using h1
  have hneg : -x ∈ F := by
    rw [← hcoeff]
    exact ((minpoly F x).coeff 0).2
  have := F.neg_mem hneg
  rwa [neg_neg] at this

end Work.DSG4b.gonfPerfect.pbAux




/-!
# Existence of `p`-bases

Given the "maximality step" — a nontrivial relation of degree `< p` between monomials over a
`p`-independent set `S` and a `p`-th root of an element outside `pSpan L p S` forces that element
into the (field!) `pSpan L p S` — we obtain a `p`-basis of `L` over `L ^ p`.

The argument is Zorn's lemma on the `p`-independent subsets of `L` (finite character, `Chain.lean`),
combined with the endgame: a maximal `p`-independent set `Λ` must span, since otherwise an element
`x ∉ pSpan L p Λ` would either be adjoinable to `Λ` (giving a larger `p`-independent set) or
satisfy a relation whose coefficients lie in the *field* `pSpan L p Λ`, forcing `x ∈ pSpan L p Λ`.

This file is self-contained apart from the input `hrel`, which is supplied by
`Work.DSG4b.gonfPerfect.pbAux.exists_relation_of_not_isPIndep_insert`.
-/

namespace Work.DSG4b.gonfPerfect.pbAux

variable (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

/-- The maximality step: if `S` is `p`-independent and `S ∪ {x}` is not, then `x` satisfies a
nontrivial relation of degree `< p` with coefficients in `pSpan L p S`. -/
abbrev MaximalityStep : Prop :=
  ∀ (S : Set L) (x : L), IsPIndep L p S → ¬ IsPIndep L p (insert x S) →
    ∃ A : Fin p → L, (∀ k, A k ∈ pSpan L p S) ∧ (∃ k, A k ≠ 0) ∧
      (∑ k : Fin p, A k * x ^ (k : ℕ)) = 0

/-- Existence of a `p`-basis of `L` over `L ^ p`, given the maximality step. -/
theorem exists_pBasis_of_relation (hrel : MaximalityStep L p) :
    ∃ (Λ : Set L) (b : Module.Basis {e : Λ →₀ ℕ // ∀ a : Λ, e a < p}
        ((frobenius L p).fieldRange) L),
      ∀ e, (b e : L) = (e.1).prod (fun a k => ((a : L) ^ k)) := by
  classical
  -- Zorn: the `p`-independent sets are of finite character
  obtain ⟨Λ, hΛmax⟩ := zorn_subset {S : Set L | IsPIndep L p S} (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · exact ⟨⋃₀ c, isPIndep_sUnion_of_isChain L p c hchain hne fun S hS => hc hS,
        fun s hs => Set.subset_sUnion_of_mem hs⟩
    · exact ⟨∅, isPIndep_empty L p, fun s hs => absurd ⟨s, hs⟩ hne⟩)
  -- a maximal `p`-independent set spans
  have hspan : pSpan L p Λ = ⊤ := by
    by_contra hne
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    have hxΛ : x ∉ Λ := fun h => hx (subset_pSpan Λ h)
    have hmax : ¬ IsPIndep L p (insert x Λ) := fun h' =>
      hxΛ (hΛmax.2 h' (fun y hy => Set.mem_insert_iff.mpr (Or.inr hy))
        (Set.mem_insert_iff.mpr (Or.inl rfl)))
    obtain ⟨A, hA, hAne, hAsum⟩ := hrel Λ x hΛmax.1 hmax
    have hmem : x ∈ pSubfield L p Λ :=
      mem_of_relation L p (pSubfield L p Λ) x
        (show x ^ p ∈ (pSpan L p Λ : Set L) from
          pSpan_algebraMap_mem L p Λ ⟨x ^ p, pow_mem_pthPowerField L p x⟩)
        A (fun k => show A k ∈ (pSpan L p Λ : Set L) from hA k) hAne hAsum
    exact hx (show x ∈ (pSpan L p Λ : Set L) from hmem)
  -- the family of monomials indexed by `Λ`
  let v : {e : Λ →₀ ℕ // ∀ a : Λ, e a < p} → L := fun e => e.1.prod fun a k => (a : L) ^ k
  have hmon : ∀ w : Λ →₀ ℕ, mon (w.mapDomain Subtype.val) = w.prod fun a k => (a : L) ^ k :=
    fun w => Finsupp.prod_mapDomain_index (fun b => pow_zero b) fun b m₁ m₂ => by rw [pow_add]
  have hli : LinearIndependent (pthPowerField L p) v := by
    let φ : {e : Λ →₀ ℕ // ∀ a : Λ, e a < p} → Idx L p Λ := fun e =>
      ⟨e.1.mapDomain Subtype.val, by
        intro y hy
        have hy' : e.1.mapDomain Subtype.val y ≠ 0 := by
          simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hy
        obtain ⟨a, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hy'
        exact a.2
      , by
        intro a
        by_cases ha : a ∈ Set.range (Subtype.val : Λ → L)
        · obtain ⟨b, rfl⟩ := ha
          simpa using e.2 b
        · rw [Finsupp.mapDomain_of_notMem_range e.1 a ha]
          exact Nat.Prime.pos (Fact.out)⟩
    have hinj : Function.Injective φ := by
      intro a b hab
      have h1 : a.1.mapDomain Subtype.val = b.1.mapDomain Subtype.val :=
        congrArg (fun w : Idx L p Λ => w.1) hab
      exact Subtype.ext (Finsupp.mapDomain_injective Subtype.val_injective h1)
    have hcomp : pMon L p Λ ∘ φ = v := by
      funext e
      exact hmon e.1
    have hli' : LinearIndependent (pthPowerField L p) (pMon L p Λ ∘ φ) :=
      hΛmax.1.comp φ hinj
    rwa [hcomp] at hli'
  have hsp : ⊤ ≤ Submodule.span (pthPowerField L p) (Set.range v) := by
    rw [← hspan]
    refine Submodule.span_le.mpr ?_
    rintro z ⟨u, rfl⟩
    have hu : (u.1.support : Set L) ⊆ Set.range (Subtype.val : Λ → L) :=
      fun y hy => ⟨⟨y, u.2.1 hy⟩, rfl⟩
    have hev : ∀ a : Λ, (u.1.comapDomain Subtype.val Subtype.val_injective.injOn) a < p :=
      fun a => by rw [Finsupp.comapDomain_apply]; exact u.2.2 (Subtype.val a)
    refine Submodule.subset_span ⟨⟨_, hev⟩, ?_⟩
    show (u.1.comapDomain Subtype.val Subtype.val_injective.injOn).prod
        (fun (a : Λ) (k : ℕ) => (a : L) ^ k) = mon u.1
    rw [← hmon (u.1.comapDomain Subtype.val Subtype.val_injective.injOn),
      Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective u.1 hu]
  exact ⟨Λ, Module.Basis.mk hli hsp, fun e => Module.Basis.mk_apply hli hsp e⟩

end Work.DSG4b.gonfPerfect.pbAux



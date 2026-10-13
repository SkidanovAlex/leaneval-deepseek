import Mathlib

namespace Work.DSG4b.pBasis

open Finsupp Module

variable {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]

/-- Exponent vectors all of whose entries are `< m`. -/
abbrev Idx (Λ : Set L) (m : ℕ) := {e : Λ →₀ ℕ // ∀ a : Λ, e a < m}

/-- The monomial `∏ a ^ (e a)`. -/
noncomputable def mono {Λ : Set L} (e : Λ →₀ ℕ) : L := e.prod (fun a k => ((a : L) ^ k))

/-- The subfield of `p ^ n`-th powers, i.e. the range of the `n`-th Frobenius. -/
abbrev K (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p] (n : ℕ) : Subfield L :=
  (iterateFrobenius L p n).fieldRange

/-- The monomial attached to a pair of exponents in the digit decomposition. -/
noncomputable def vprod (Λ : Set L) (p n : ℕ) : Idx Λ p × Idx Λ (p ^ n) → L :=
  fun ef => mono (ef.1.1 + p • ef.2.1)

lemma vprod_apply (Λ : Set L) (p n : ℕ) (ef : Idx Λ p × Idx Λ (p ^ n)) :
    vprod Λ p n ef = mono (ef.1.1 + p • ef.2.1) := rfl

@[simp]
lemma mono_zero {Λ : Set L} : mono (0 : Λ →₀ ℕ) = 1 := Finsupp.prod_zero_index

lemma mono_add {Λ : Set L} (e f : Λ →₀ ℕ) : mono (e + f) = mono e * mono f :=
  Finsupp.prod_add_index' (fun a => pow_zero _) (fun a b c => pow_add _ _ _)

lemma mono_nsmul {Λ : Set L} (k : ℕ) (e : Λ →₀ ℕ) : mono (k • e) = (mono e) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, mono_add, ih, pow_succ]

lemma finset_sum_pow {ι : Type*} (s : Finset ι) (Y : ι → L) :
    (∑ i ∈ s, Y i) ^ p = ∑ i ∈ s, (Y i) ^ p := by
  rw [← frobenius_def, map_sum]
  simp [frobenius_def]

lemma finsupp_sum_pow {ι M : Type*} [Zero M] (s : ι →₀ M) (Y : ι → L) :
    (s.sum (fun i _ => Y i)) ^ p = s.sum (fun i _ => (Y i) ^ p) := by
  simp only [Finsupp.sum]
  rw [finset_sum_pow]

lemma mem_K (n : ℕ) (x : L) : x ∈ K L p n ↔ ∃ y : L, y ^ p ^ n = x := by
  change x ∈ (iterateFrobenius L p n).fieldRange ↔ _
  rw [RingHom.mem_fieldRange]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [← hy, iterateFrobenius_def]⟩
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [iterateFrobenius_def, hy]⟩

lemma mem_K_succ (n : ℕ) (x : L) : x ∈ K L p (n + 1) ↔ ∃ y ∈ K L p n, y ^ p = x := by
  rw [mem_K]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ^ p ^ n, ?_, ?_⟩
    · exact (mem_K n _).mpr ⟨y, rfl⟩
    · rw [← pow_mul, ← pow_succ, hy]
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨z, hz⟩ := (mem_K n y).mp hy
    refine ⟨z, ?_⟩
    rw [← hyx, ← hz, ← pow_mul, ← pow_succ]

lemma K_one_eq : K L p 1 = (frobenius L p).fieldRange := by
  show (iterateFrobenius L p 1).fieldRange = (frobenius L p).fieldRange
  rw [iterateFrobenius_one]

lemma K_zero_eq : K L p 0 = (⊤ : Subfield L) := by
  show (iterateFrobenius L p 0).fieldRange = ⊤
  rw [iterateFrobenius_zero, RingHom.fieldRange_eq_top_iff]
  exact fun x => ⟨x, rfl⟩

lemma exists_pow_eq_of_mem_K_one {x : L} (hx : x ∈ K L p 1) : ∃ y : L, y ^ p = x := by
  rw [mem_K] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, by rwa [pow_one] at hy⟩

/-- Transport of a basis along an equality of the field of scalars. -/
lemma basis_subfield_congr {ι : Type*} {s t : Subfield L} (h : s = t)
    (B : Module.Basis ι s L) : ∃ B' : Module.Basis ι t L, ∀ i, (B' i : L) = (B i : L) := by
  subst h
  exact ⟨B, fun i => rfl⟩

/-- The "carry-free sum" map `(e, f) ↦ e + p • f` for exponent vectors. -/
noncomputable def digitUp (α : Type*) (p n : ℕ) (hp : 0 < p) :
    {e : α →₀ ℕ // ∀ a, e a < p} × {e : α →₀ ℕ // ∀ a, e a < p ^ n} →
      {e : α →₀ ℕ // ∀ a, e a < p ^ (n + 1)} :=
  fun ef => ⟨ef.1.1 + p • ef.2.1, fun a => by
    rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, pow_succ]
    have h1 : ef.1.1 a < p := ef.1.2 a
    have h2 : ef.2.1 a + 1 ≤ p ^ n := by have := ef.2.2 a; omega
    calc ef.1.1 a + p * ef.2.1 a
        < p + p * ef.2.1 a := by omega
      _ = p * (ef.2.1 a + 1) := by ring
      _ ≤ p * p ^ n := Nat.mul_le_mul_left p h2
      _ = p ^ n * p := by ring⟩

/-- The digit map `s ↦ (s mod p, s / p)`. -/
noncomputable def digitDown (α : Type*) (p n : ℕ) (hp : 0 < p) :
    {e : α →₀ ℕ // ∀ a, e a < p ^ (n + 1)} →
      {e : α →₀ ℕ // ∀ a, e a < p} × {e : α →₀ ℕ // ∀ a, e a < p ^ n} :=
  fun s =>
    (⟨s.1.mapRange (· % p) (Nat.zero_mod p), fun a => by
        rw [Finsupp.mapRange_apply]; exact Nat.mod_lt _ hp⟩,
     ⟨s.1.mapRange (· / p) (Nat.zero_div p), fun a => by
        rw [Finsupp.mapRange_apply, Nat.div_lt_iff_lt_mul hp]
        simpa only [pow_succ] using s.2 a⟩)

lemma digitUp_apply (α : Type*) (p n : ℕ) (hp : 0 < p)
    (ef : {e : α →₀ ℕ // ∀ a, e a < p} × {e : α →₀ ℕ // ∀ a, e a < p ^ n}) :
    (digitUp α p n hp ef).1 = ef.1.1 + p • ef.2.1 := rfl

lemma digitDown_fst (α : Type*) (p n : ℕ) (hp : 0 < p)
    (s : {e : α →₀ ℕ // ∀ a, e a < p ^ (n + 1)}) :
    ((digitDown α p n hp s).1 : α →₀ ℕ) = s.1.mapRange (· % p) (Nat.zero_mod p) := rfl

lemma digitDown_snd (α : Type*) (p n : ℕ) (hp : 0 < p)
    (s : {e : α →₀ ℕ // ∀ a, e a < p ^ (n + 1)}) :
    ((digitDown α p n hp s).2 : α →₀ ℕ) = s.1.mapRange (· / p) (Nat.zero_div p) := rfl

/-- **Digit decomposition.**  The maps `g ↦ g mod p` and `g ↦ g / p` give a bijection
`{g // ∀ a, g a < p ^ (n+1)} ≃ {e // ∀ a, e a < p} × {f // ∀ a, f a < p ^ n}`; the inverse is
`(e, f) ↦ e + p • f`. -/
theorem expEquiv_spec (α : Type*) (p n : ℕ) (hp : 0 < p) :
    ∃ E : {e : α →₀ ℕ // ∀ a, e a < p ^ (n + 1)} ≃
          {e : α →₀ ℕ // ∀ a, e a < p} × {e : α →₀ ℕ // ∀ a, e a < p ^ n},
      (∀ s, (E s).1.1 + p • (E s).2.1 = s.1) ∧
      (∀ (e : {e : α →₀ ℕ // ∀ a, e a < p}) (f : {e : α →₀ ℕ // ∀ a, e a < p ^ n}),
        (E.symm (e, f) : {e : α →₀ ℕ // ∀ a, e a < p ^ (n + 1)}).1 = e.1 + p • f.1) := by
  have hleft : Function.LeftInverse (digitUp α p n hp) (digitDown α p n hp) := fun s => by
    refine Subtype.ext (Finsupp.ext (fun a => ?_))
    rw [digitUp_apply, digitDown_fst, digitDown_snd]
    rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply]
    exact Nat.mod_add_div (s.1 a) p
  have hright : Function.RightInverse (digitUp α p n hp) (digitDown α p n hp) := fun ef => by
    refine Prod.ext ?_ ?_ <;> refine Subtype.ext (Finsupp.ext (fun a => ?_))
    · rw [digitDown_fst, digitUp_apply, Finsupp.mapRange_apply]
      rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ef.1.2 a)]
    · rw [digitDown_snd, digitUp_apply, Finsupp.mapRange_apply]
      rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (ef.1.2 a), zero_add]
  refine ⟨Equiv.mk (digitDown α p n hp) (digitUp α p n hp) hleft hright, ?_, ?_⟩
  · intro s
    exact congrArg Subtype.val (hleft s)
  · intro e f
    exact digitUp_apply α p n hp (e, f)

/-- The inductive step: a `p`-basis over `L ^ p` and a `p ^ n`-basis over `L ^ (p ^ n)` combine to
a `p ^ (n+1)`-basis over `L ^ (p ^ (n+1))`. -/
theorem pBasis_step {Λ : Set L} {b : Module.Basis (Idx Λ p) ((frobenius L p).fieldRange) L}
    (hb : ∀ e, (b e : L) = mono e.1) {n : ℕ}
    (bn : Module.Basis (Idx Λ (p ^ n)) (K L p n) L) (hbn : ∀ e, (bn e : L) = mono e.1) :
    ∃ b' : Module.Basis (Idx Λ (p ^ (n + 1))) (K L p (n + 1)) L,
      ∀ e, (b' e : L) = mono e.1 := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  obtain ⟨b1, hb1⟩ := basis_subfield_congr (K_one_eq (L := L) (p := p)).symm b
  have hb1' : ∀ e : Idx Λ p, (b1 e : L) = mono e.1 := fun e => (hb1 e).trans (hb e)
  have hlin_1 : LinearIndependent (K L p 1) (fun e : Idx Λ p => mono e.1) := by
    have h : (fun e : Idx Λ p => (b1 e : L)) = fun e => mono e.1 := funext hb1'
    rw [← h]; exact b1.linearIndependent
  have hlin_n : LinearIndependent (K L p n) (fun f : Idx Λ (p ^ n) => mono f.1) := by
    have h : (fun f : Idx Λ (p ^ n) => (bn f : L)) = fun f => mono f.1 := funext hbn
    rw [← h]; exact bn.linearIndependent
  -- ### span of the product-indexed family
  have hspan_v : ⊤ ≤ Submodule.span (K L p (n + 1)) (Set.range (vprod Λ p n)) := by
    intro x _
    have hx1 : x = (b1.repr x).sum (fun e c => (c : L) * mono e.1) := by
      conv_lhs => rw [← Module.Basis.linearCombination_repr b1 x]
      rw [Finsupp.linearCombination_apply]
      refine Finsupp.sum_congr (fun e _ => ?_)
      rw [hb1' e, Algebra.smul_def, Subfield.algebraMap_ofSubfield, Subfield.subtype_apply]
    have hroot : ∀ e : Idx Λ p, ∃ y : L, y ^ p = (((b1.repr x) e : K L p 1) : L) :=
      fun e => exists_pow_eq_of_mem_K_one (b1.repr x e).2
    choose d hd using hroot
    have hx2 : x = (b1.repr x).sum (fun e _ => (d e) ^ p * mono e.1) := by
      conv_lhs => rw [hx1]
      refine Finsupp.sum_congr (fun e _ => ?_)
      rw [hd e]
    have hde : ∀ e : Idx Λ p,
        d e = (bn.repr (d e)).sum (fun f q => ((q : K L p n) : L) * mono f.1) := by
      intro e
      conv_lhs => rw [← Module.Basis.linearCombination_repr bn (d e)]
      rw [Finsupp.linearCombination_apply]
      refine Finsupp.sum_congr (fun f _ => ?_)
      rw [hbn f, Algebra.smul_def, Subfield.algebraMap_ofSubfield, Subfield.subtype_apply]
    have hpow : ∀ e : Idx Λ p, (d e) ^ p =
        (bn.repr (d e)).sum (fun f q => ((q : K L p n) : L) ^ p * mono (p • f.1)) := by
      intro e
      conv_lhs => rw [hde e, ← frobenius_def]
      simp only [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      rw [frobenius_def, mul_pow, ← mono_nsmul]
    have hx3 : x = (b1.repr x).sum (fun e _ =>
        (bn.repr (d e)).sum (fun f q => ((q : K L p n) : L) ^ p * mono (e.1 + p • f.1))) := by
      conv_lhs => rw [hx2]
      refine Finsupp.sum_congr (fun e _ => ?_)
      rw [hpow e, Finsupp.sum_mul]
      refine Finsupp.sum_congr (fun f _ => ?_)
      rw [mul_assoc, ← mono_add, add_comm]
    rw [hx3]
    refine Submodule.sum_mem _ (fun e _ => ?_)
    simp only [Finsupp.sum]
    refine Submodule.sum_mem _ (fun f _ => ?_)
    refine Submodule.smul_mem _ (⟨(((bn.repr (d e)) f : K L p n) : L) ^ p,
        (mem_K_succ n _).mpr ⟨(((bn.repr (d e)) f : K L p n) : L),
          ((bn.repr (d e)) f).2, rfl⟩⟩ : K L p (n + 1))
      (Submodule.subset_span ⟨(e, f), rfl⟩)
  -- ### linear independence of the product-indexed family
  have hlin_v : LinearIndependent (K L p (n + 1)) (vprod Λ p n) := by
    rw [linearIndependent_iff]
    intro l hl
    set lc := l.curry with hlc
    have hl' : lc.sum (fun e f' => f'.sum (fun f c => c • vprod Λ p n (e, f))) = 0 := by
      rw [Finsupp.linearCombination_apply] at hl
      have hlu : l = lc.uncurry := (hlc ▸ Finsupp.uncurry_curry l).symm
      rw [hlu] at hl
      rw [← hl]
      exact (Finsupp.sum_uncurry_index' lc (fun e f c => c • vprod Λ p n (e, f))).symm
    have hroot : ∀ e : Idx Λ p, ∀ f : Idx Λ (p ^ n), ∃ y : K L p n,
        ((y : K L p n) : L) ^ p = (((lc e) f : K L p (n + 1)) : L) := by
      intro e f
      obtain ⟨y, hy, hyx⟩ := (mem_K_succ n _).mp ((lc e) f).2
      exact ⟨⟨y, hy⟩, hyx⟩
    choose g hg using hroot
    set A : Idx Λ p → L := fun e =>
      ((lc e).support).sum (fun f => ((g e f : K L p n) : L) * mono f.1) with hA
    have hinner : ∀ e : Idx Λ p,
        (lc e).sum (fun f c => c • vprod Λ p n (e, f)) = mono e.1 * (A e) ^ p := by
      intro e
      have h1 : (lc e).sum (fun f c => c • vprod Λ p n (e, f))
          = (lc e).sum (fun f c => mono e.1 * (((c : K L p (n + 1)) : L) * mono (p • f.1))) := by
        refine Finsupp.sum_congr (fun f _ => ?_)
        rw [vprod_apply, Algebra.smul_def, Subfield.algebraMap_ofSubfield, Subfield.subtype_apply,
          mono_add]
        ring
      have h2 : (lc e).sum (fun f c => mono e.1 * (((c : K L p (n + 1)) : L) * mono (p • f.1)))
          = mono e.1 * (lc e).sum (fun f c => ((c : K L p (n + 1)) : L) * mono (p • f.1)) := by
        rw [Finsupp.mul_sum]
      have h3 : (lc e).sum (fun f c => ((c : K L p (n + 1)) : L) * mono (p • f.1))
          = (lc e).sum (fun f c => ((g e f : K L p n) : L) ^ p * mono (p • f.1)) := by
        refine Finsupp.sum_congr (fun f _ => ?_)
        rw [hg e f]
      have h4 : (lc e).sum (fun f c => ((g e f : K L p n) : L) ^ p * mono (p • f.1))
          = (lc e).sum (fun f c => (((g e f : K L p n) : L) * mono f.1) ^ p) := by
        refine Finsupp.sum_congr (fun f _ => ?_)
        rw [mul_pow, ← mono_nsmul]
      have h5 : (lc e).sum (fun f c => (((g e f : K L p n) : L) * mono f.1) ^ p)
          = ((lc e).sum (fun f c => ((g e f : K L p n) : L) * mono f.1)) ^ p :=
        (finsupp_sum_pow (lc e) (fun f => ((g e f : K L p n) : L) * mono f.1)).symm
      have h6 : (lc e).sum (fun f c => ((g e f : K L p n) : L) * mono f.1) = A e := by
        rw [hA]; rfl
      rw [h1, h2, h3, h4, h5, h6]
    have hrel : lc.sum (fun e _ => mono e.1 * (A e) ^ p) = 0 := by
      rw [← hl']
      exact Finsupp.sum_congr (fun e _ => (hinner e).symm)
    have hrel' : ((lc.support).sum (fun e => (A e) ^ p * mono e.1)) = 0 := by
      have hsum : lc.sum (fun e _ => mono e.1 * (A e) ^ p)
          = (lc.support).sum (fun e => mono e.1 * (A e) ^ p) := by
        simp only [Finsupp.sum]
      rw [hsum] at hrel
      rw [← hrel]
      exact Finset.sum_congr rfl (fun e _ => mul_comm _ _)
    have hC : ∀ e ∈ lc.support,
        (⟨(A e) ^ p, (mem_K (p := p) 1 ((A e) ^ p)).mpr ⟨A e, by rw [pow_one]⟩⟩ :
          K L p 1) = 0 := by
      refine (linearIndependent_iff'.mp hlin_1 lc.support (fun e =>
        (⟨(A e) ^ p, (mem_K (p := p) 1 ((A e) ^ p)).mpr ⟨A e, by rw [pow_one]⟩⟩ :
          K L p 1))) ?_
      have hsum : (∑ e ∈ lc.support,
            (⟨(A e) ^ p, (mem_K (p := p) 1 ((A e) ^ p)).mpr ⟨A e, by rw [pow_one]⟩⟩ :
              K L p 1) • mono e.1)
          = ∑ e ∈ lc.support, (A e) ^ p * mono e.1 := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Algebra.smul_def, Subfield.algebraMap_ofSubfield]
        rfl
      rw [hsum, hrel']
    have hA0 : ∀ e : Idx Λ p, A e = 0 := by
      intro e
      by_cases he : e ∈ lc.support
      · have h := hC e he
        have h0 : (A e) ^ p = 0 := by
          have h1 := congrArg (fun x : K L p 1 => (x : L)) h
          simpa using h1
        by_contra hne
        exact (pow_ne_zero p hne) h0
      · have h0 : lc e = 0 := by
          by_contra hle
          exact he ((Finsupp.mem_support_iff (f := lc) (a := e)).mpr hle)
        simp [hA, h0]
    have hg0 : ∀ e : Idx Λ p, ∀ f : Idx Λ (p ^ n), g e f = 0 := by
      intro e f
      by_cases hf : f ∈ (lc e).support
      · have hsum : (∑ f' ∈ (lc e).support, g e f' • mono f'.1) = 0 := by
          rw [← hA0 e]
          simp only [hA]
          refine Finset.sum_congr rfl (fun f' _ => ?_)
          rw [Algebra.smul_def, Subfield.algebraMap_ofSubfield]
          rfl
        exact (linearIndependent_iff'.mp hlin_n (lc e).support (g e)) hsum f hf
      · have h1 : lc e f = 0 := by
          by_contra hf'
          exact hf ((Finsupp.mem_support_iff (f := lc e) (a := f)).mpr hf')
        have h0 : (((g e f : K L p n) : L)) ^ p = 0 := by
          rw [hg e f, h1]; rfl
        have hL : ((g e f : K L p n) : L) = 0 := by
          by_contra hne
          exact (pow_ne_zero p hne) h0
        exact Subtype.coe_injective (by simpa using hL)
    have hlc0 : lc = 0 := by
      refine Finsupp.ext (fun e => ?_)
      refine Finsupp.ext (fun f => ?_)
      have h1 : (((lc e) f : K L p (n + 1)) : L) = 0 := by
        rw [← hg e f, hg0 e f, Subfield.coe_zero, zero_pow hp0]
      exact Subtype.coe_injective (by simpa using h1)
    have hl0 : l = 0 := by
      have h : l = lc.uncurry := (hlc ▸ Finsupp.uncurry_curry l).symm
      rw [h, hlc0]
      ext x
      simp [Finsupp.uncurry_apply]
    exact hl0
  -- ### assemble
  set B : Module.Basis (Idx Λ p × Idx Λ (p ^ n)) (K L p (n + 1)) L :=
    Module.Basis.mk hlin_v hspan_v with hB
  obtain ⟨E, hE1, -⟩ := expEquiv_spec (↥Λ) p n (Fact.out : Nat.Prime p).pos
  refine ⟨B.reindex E.symm, fun s => ?_⟩
  show ((B.reindex E.symm) s : L) = mono s.1
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB, Module.Basis.mk_apply, vprod_apply, hE1 s]

/-- **A `p`-basis is a `p ^ n`-basis.**  Let `L` be a field of characteristic a prime `p` and let
`Λ ⊆ L` be a `p`-basis of `L` over `L ^ p`, exhibited by the monomial basis `b` of `L` over the
subfield `L ^ p` of `p`-th powers.  Then for every `n` the monomials of exponents `< p ^ n` form a
basis of `L` over the subfield `L ^ (p ^ n)` (the range of the `n`-th iterate of the Frobenius). -/
theorem pBasis_pow_basis (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (Λ : Set L)
    (b : Module.Basis {e : Λ →₀ ℕ // ∀ a : Λ, e a < p} ((frobenius L p).fieldRange) L)
    (hb : ∀ e, (b e : L) = (e.1).prod (fun a k => ((a : L) ^ k))) (n : ℕ) :
    ∃ b' : Module.Basis {e : Λ →₀ ℕ // ∀ a : Λ, e a < p ^ n}
        ((iterateFrobenius L p n).fieldRange) L,
      ∀ e, (b' e : L) = (e.1).prod (fun a k => ((a : L) ^ k)) := by
  classical
  have hP0 : ∃ b' : Module.Basis (Idx Λ (p ^ 0)) (K L p 0) L, ∀ e, (b' e : L) = mono e.1 := by
    haveI : Unique (Idx Λ (p ^ 0)) :=
      { default := ⟨0, by simp⟩
        uniq := fun e => Subtype.ext (Finsupp.ext (fun a => by
          have h : e.1 a < 1 := by simpa using e.2 a
          have h0 : ((⟨0, by simp⟩ : Idx Λ (p ^ 0)) : Λ →₀ ℕ) a = 0 := by simp
          omega)) }
    have hKeq : K L p 0 = ⊤ := K_zero_eq
    have hbij : Function.Bijective (Algebra.linearMap (K L p 0) L) := by
      refine ⟨fun a b hab => Subtype.ext ?_,
        fun x => ⟨⟨x, by rw [hKeq]; exact Subfield.mem_top x⟩, ?_⟩⟩
      · simpa using hab
      · rfl
    refine ⟨(Module.Basis.singleton (Idx Λ (p ^ 0)) (K L p 0)).map
      (LinearEquiv.ofBijective (Algebra.linearMap (K L p 0) L) hbij), fun e => ?_⟩
    rw [Module.Basis.map_apply, Module.Basis.singleton_apply, LinearEquiv.ofBijective_apply]
    have he : e.1 = 0 := Finsupp.ext (fun a => by
      have h : e.1 a < 1 := by simpa using e.2 a
      simp only [Finsupp.zero_apply]
      omega)
    rw [he, mono_zero]
    simp [Algebra.linearMap_apply, Subfield.algebraMap_ofSubfield]
  have hstep : ∀ n, (∃ b' : Module.Basis (Idx Λ (p ^ n)) (K L p n) L,
        ∀ e, (b' e : L) = mono e.1) →
      (∃ b' : Module.Basis (Idx Λ (p ^ (n + 1))) (K L p (n + 1)) L,
        ∀ e, (b' e : L) = mono e.1) := by
    intro n h
    obtain ⟨bn, hbn⟩ := h
    exact pBasis_step (b := b) hb bn hbn
  obtain ⟨b', hb'⟩ := Nat.rec (motive := fun m =>
      ∃ b' : Module.Basis (Idx Λ (p ^ m)) (K L p m) L, ∀ e, (b' e : L) = mono e.1) hP0 hstep n
  exact ⟨b', fun e => hb' e⟩

end Work.DSG4b.pBasis

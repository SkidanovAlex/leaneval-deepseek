import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.BSLit.Wielandt.TIInfBot
import Submission.Work.BSLit.Wielandt.FrobeniusRelation
import Submission.Work.BSLit.Wielandt.linearFormCountingFormula

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

universe u v

namespace Work.BSLit.Wielandt

/-! ## Elementary abelian `q`-groups as `𝔽_q`-modules -/

/-- The `𝔽_q`-module structure on (the additive group underlying) a commutative group all of whose
elements satisfy `m ^ q = 1` (`q` a prime). -/
noncomputable def zmodModuleOfExpFSC {M : Type*} [CommGroup M] (q : ℕ)
    (hexp : ∀ m : M, m ^ q = 1) : Module (ZMod q) (Additive M) :=
  AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hexp x.toMul]
    rfl

/-- A conjugate subgroup has the same cardinality. -/
theorem card_map_conjFSC {F : Type*} [Group F] (H : Subgroup F) (x : F) :
    Nat.card ↥(H.map (MulAut.conj x).toMonoidHom) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
    (MulEquiv.injective (MulAut.conj x))

/-- `C_M(H^x)` has the same cardinality as `C_M(H)`. -/
theorem card_fixedBy_map_conjFSC {F M : Type*} [Group F] [Group M] (ρ : F →* MulAut M)
    (H : Subgroup F) (x : F) :
    Nat.card (fixedBy ρ (H.map (MulAut.conj x).toMonoidHom)) = Nat.card (fixedBy ρ H) := by
  rw [fixedBy_map_conj]
  exact Subgroup.card_map_of_injective (f := (ρ x).toMonoidHom) (MulEquiv.injective (ρ x))

/-- `C_M(⊥) = M`. -/
theorem card_fixedBy_botFSC {F M : Type*} [Group F] [Group M] (ρ : F →* MulAut M) :
    Nat.card (fixedBy ρ (⊥ : Subgroup F)) = Nat.card M := by
  rw [fixedBy_bot, Subgroup.card_top]

/-- `1_⊥ = 1` in `ℤ[F]`. -/
theorem groupSum_bot_eq_oneFSC {F : Type*} [Group F] [Fintype F] :
    Work.BSLit.groupSum (⊥ : Subgroup F) = (1 : MonoidAlgebra ℤ F) := by
  have h1 : ∀ h : ↥(⊥ : Subgroup F), ((h : F)) = 1 := fun h => Subgroup.mem_bot.mp h.2
  simp [Work.BSLit.groupSum, h1, MonoidAlgebra.one_def]

/-- `C_M(H₂) ≤ C_M(H₁)` for `H₁ ≤ H₂`. -/
theorem fixedBy_le_fixedByFSC {F M : Type*} [Group F] [Group M] (ρ : F →* MulAut M)
    {H₁ H₂ : Subgroup F} (h : H₁ ≤ H₂) : fixedBy ρ H₂ ≤ fixedBy ρ H₁ :=
  fun _ hq g hg => hq g (h hg)

/-! ## The exactness input: the linear form of Wielandt's counting lemma -/

/-- **The linear form of Wielandt's counting lemma (Huppert–Blackburn XI 12.4), `ι`-indexed.**

Let `F` be a finite group, `q` a prime with `q ∤ |F|`, and `ρ` a finite-dimensional
`𝔽_q`-representation of `F`.  If `∑ i, n i • 1_{H i} = 0` in `ℤ[F]` (with
`1_H = Work.BSLit.groupSum H = ∑_{h ∈ H} h`), then
`∑ i, n i * |H i| * dim_{𝔽_q} V^{H i} = 0`, where `V^H` is `Representation.invariants (ρ.comp
H.subtype)`.

This is the "exact orthogonality of the lifted trace" (Huppert–Blackburn XI 12.4); it is proved
independently as `Work.BSLit.Wielandt.linearFormCountingFormula`. -/
theorem hLin_wielandt {F : Type*} [Group F] [Fintype F] {q : ℕ} [Fact q.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
    (ρ : Representation (ZMod q) F V) (hq : ¬ q ∣ Nat.card F)
    {ι : Type*} [Fintype ι] (H : ι → Subgroup F) (n : ι → ℤ)
    (hrel : ∑ i, n i • Work.BSLit.groupSum (H i) = 0) :
    ∑ i, n i * (Nat.card (H i) : ℤ) *
      (Module.finrank (ZMod q) ↥(Representation.invariants (ρ.comp (H i).subtype)) : ℤ) = 0 :=
  linearFormCountingFormula ρ hq H n hrel

/-! ## The `F`-simple elementary abelian case

The proof only uses that `M` is an `𝔽_q`-module (`q ∤ |F|`), that `C_M(K) = 1` (which also forces
`C_M(F) = 1`) and the Frobenius relation
`Σ_{x ∈ K} 1_{P^x} + 1_K = 1_F + |K| · 1` of `Work.BSLit.Wielandt.FrobeniusRelation`: evaluating that
relation through the linear form of Wielandt's counting lemma
(`Work.BSLit.Wielandt.linearFormCountingFormula`) gives `|K| · (|P| · dim M^P - dim M) = 0`, i.e.
`dim M = |P| · dim M^P`.  -/
theorem frobeniusFSimpleCase_aux {F : Type v} {M : Type u} [Group F] [Fintype F] [CommGroup M]
    [Finite M] {q p : ℕ} [Fact q.Prime] (hexp : ∀ m : M, m ^ q = 1) (hp : p.Prime)
    (ρ : F →* MulAut M) (hq : ¬ q ∣ Nat.card F)
    (hsimple : ∀ N : Subgroup M, (∀ g : F, N.map (ρ g) = N) → N = ⊥ ∨ N = ⊤)
    (K P : Subgroup F) (hsup : K ⊔ P = ⊤) (hcardP : Nat.card P = p)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hTI : ∀ k ∈ K, k ≠ 1 → P ⊓ P.map (MulAut.conj k⁻¹).toMonoidHom = ⊥)
    (hCK : ∀ m : M, (∀ k ∈ K, (ρ k) m = m) → m = 1)
    (hLin : ∀ {V : Type u} [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
      (σ : Representation (ZMod q) F V) {ι : Type v} [Fintype ι] (H : ι → Subgroup F) (n : ι → ℤ),
        (∑ i, n i • Work.BSLit.groupSum (H i)) = 0 →
        ∑ i, n i * (Nat.card (H i) : ℤ) *
          (Module.finrank (ZMod q) ↥(Representation.invariants (σ.comp (H i).subtype)) : ℤ) = 0) :
    (Nat.card (fixedBy ρ P)) ^ (Nat.card P * Nat.card K) * (Nat.card (fixedBy ρ K)) ^ Nat.card K
      = (Nat.card (fixedBy ρ ⊤)) ^ (Nat.card P * Nat.card K) * (Nat.card M) ^ Nat.card K := by
  classical
  -- the `𝔽_q`-module structure on `Additive M` and the induced representation
  letI : Module (ZMod q) (Additive M) := zmodModuleOfExpFSC q hexp
  let ρ' : Representation (ZMod q) F (Additive M) :=
    { toFun := fun g =>
        AddMonoidHom.toZModLinearMap q
          { toFun := fun x : Additive M => Additive.ofMul (ρ g x.toMul)
            map_zero' := by simp
            map_add' := by intro a b; simp [toMul_add, map_mul] }
      map_one' := by ext x; simp
      map_mul' := by intro g h; ext x; simp [MulAut.mul_apply] }
  haveI : Fintype (Additive M) := Fintype.ofFinite (Additive M)
  -- cardinality of the fixed point subgroup equals `q ^ (finrank of the invariants)`
  have hcard : ∀ H : Subgroup F, Nat.card (fixedBy ρ H) = q ^ Module.finrank (ZMod q)
      ↥(Representation.invariants (ρ'.comp H.subtype)) := by
    intro H
    have he : ↥(fixedBy ρ H) ≃ ↥(Representation.invariants (ρ'.comp H.subtype)) :=
      { toFun := fun x =>
          ⟨Additive.ofMul (x : M), by
            rw [Representation.mem_invariants]
            intro h
            change Additive.ofMul (ρ (h : F) (x : M)) = Additive.ofMul (x : M)
            exact congrArg Additive.ofMul (x.2 (h : F) h.2)⟩
        invFun := fun x =>
          ⟨Additive.toMul x.1, by
            rw [mem_fixedBy]
            intro h hh
            change (ρ h) (Additive.toMul x.1) = Additive.toMul x.1
            exact congrArg Additive.toMul
              ((Representation.mem_invariants (ρ := ρ'.comp H.subtype) x.1).mp x.2 ⟨h, hh⟩)⟩
        left_inv := fun x => by ext; simp
        right_inv := fun x => by ext; simp }
    rw [Nat.card_congr he, Nat.card_eq_fintype_card]
    have hfin := Module.card_eq_pow_finrank (K := ZMod q)
      (V := ↥(Representation.invariants (ρ'.comp H.subtype)))
    rwa [ZMod.card] at hfin
  -- `C_M(K) = 1` and `C_M(F) = 1`
  have hfixK : fixedBy ρ K = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Subgroup.mem_bot]
    exact hCK m (fun k hk => (mem_fixedBy.mp hm) k hk)
  have hcardK : Nat.card (fixedBy ρ K) = 1 := by rw [hfixK, Subgroup.card_bot]
  have hfixTop : fixedBy ρ ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Subgroup.mem_bot]
    exact hCK m (fun k hk => (mem_fixedBy.mp hm) k (Subgroup.mem_top k))
  have hcardTop : Nat.card (fixedBy ρ ⊤) = 1 := by rw [hfixTop, Subgroup.card_bot]
  -- the relevant invariant submodules
  have hinvK : Representation.invariants (ρ'.comp K.subtype) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv' : Additive.toMul v = 1 := by
      refine hCK (Additive.toMul v) (fun k hk => ?_)
      have h := (Representation.mem_invariants (ρ := ρ'.comp K.subtype) v).mp hv ⟨k, hk⟩
      exact congrArg Additive.toMul h
    have hv0 : v = 0 := by
      rw [← ofMul_toMul v, hv']
      rfl
    simpa using hv0
  have hinvTop : Representation.invariants (ρ'.comp (⊤ : Subgroup F).subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h2 : v ∈ Representation.invariants (ρ'.comp K.subtype) := by
      rw [Representation.mem_invariants] at hv ⊢
      intro k
      exact hv ⟨(k : F), Subgroup.mem_top _⟩
    rw [hinvK] at h2
    simpa using h2
  have hinvBot : Representation.invariants (ρ'.comp (⊥ : Subgroup F).subtype) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [Representation.mem_invariants]
    intro g
    have hg : (g : F) = 1 := Subgroup.mem_bot.mp g.2
    simp [hg]
  -- the dimension of the fixed space of every conjugate of `P` equals that of `P`
  have hconj : ∀ x : F, Module.finrank (ZMod q)
      ↥(Representation.invariants (ρ'.comp (P.map (MulAut.conj x).toMonoidHom).subtype))
        = Module.finrank (ZMod q) ↥(Representation.invariants (ρ'.comp P.subtype)) := by
    intro x
    have h1 := hcard (P.map (MulAut.conj x).toMonoidHom)
    have h2 := hcard P
    have h3 : Nat.card (fixedBy ρ (P.map (MulAut.conj x).toMonoidHom)) = Nat.card (fixedBy ρ P) :=
      card_fixedBy_map_conjFSC ρ P x
    rw [h3] at h1
    have hpow : q ^ Module.finrank (ZMod q)
          ↥(Representation.invariants (ρ'.comp (P.map (MulAut.conj x).toMonoidHom).subtype))
        = q ^ Module.finrank (ZMod q) ↥(Representation.invariants (ρ'.comp P.subtype)) := by
      rw [← h1, ← h2]
    rcases lt_trichotomy (Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ'.comp (P.map (MulAut.conj x).toMonoidHom).subtype)))
        (Module.finrank (ZMod q) ↥(Representation.invariants (ρ'.comp P.subtype))) with h | h | h
    · exact absurd hpow (by
        intro hc
        have := Nat.pow_lt_pow_right (Fact.out : q.Prime).one_lt h
        omega)
    · exact h
    · exact absurd hpow (by
        intro hc
        have := Nat.pow_lt_pow_right (Fact.out : q.Prime).one_lt h
        omega)
  -- the Frobenius relation, reindexed
  let G : (↥K ⊕ Fin 3) → Subgroup F :=
    Sum.elim (fun x : ↥K => P.map (MulAut.conj ((x : F))))
      (Fin.cases K (Fin.cases (⊤ : Subgroup F) (fun _ => (⊥ : Subgroup F))))
  let nn : (↥K ⊕ Fin 3) → ℤ :=
    Sum.elim (fun _ : ↥K => (1 : ℤ))
      (Fin.cases 1 (Fin.cases (-1) (fun _ => -(Nat.card K : ℤ))))
  have hG0 : G (Sum.inr 0) = K := rfl
  have hG1 : G (Sum.inr 1) = (⊤ : Subgroup F) := rfl
  have hG2 : G (Sum.inr 2) = (⊥ : Subgroup F) := rfl
  have hn0 : nn (Sum.inr 0) = 1 := rfl
  have hn1 : nn (Sum.inr 1) = -1 := rfl
  have hn2 : nn (Sum.inr 2) = -(Nat.card K : ℤ) := rfl
  have hrel : (∑ i, nn i • Work.BSLit.groupSum (G i)) = 0 := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_three]
    have hleft : (∑ x : ↥K, nn (Sum.inl x) • Work.BSLit.groupSum (G (Sum.inl x)))
        = Work.BSLit.conjSum K P := by
      rw [Work.BSLit.conjSum]
      exact Finset.sum_congr rfl fun x _ => by simp [G, nn, Sum.elim_inl]
    rw [hleft, hG0, hG1, hG2, hn0, hn1, hn2, groupSum_bot_eq_oneFSC]
    simp only [one_smul, neg_smul, one_smul]
    have hshape : Work.BSLit.conjSum K P +
          ((Work.BSLit.groupSum K + -Work.BSLit.groupSum (⊤ : Subgroup F)) +
            -((Nat.card K : ℤ) • (1 : MonoidAlgebra ℤ F)))
        = (Work.BSLit.conjSum K P + Work.BSLit.groupSum K) -
          (Work.BSLit.groupSum (⊤ : Subgroup F) + (Nat.card K : ℤ) • (1 : MonoidAlgebra ℤ F)) := by
      abel
    rw [hshape, FrobeniusRelation K P hsup hnorm hTI, sub_self]
  -- the linear form of Wielandt's counting lemma
  have hlin := hLin ρ' (ι := ↥K ⊕ Fin 3) G nn hrel
  -- evaluate the terms of the sum
  have hterm : ∀ x : ↥K, nn (Sum.inl x) * (Nat.card (G (Sum.inl x)) : ℤ) *
      (Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ'.comp (G (Sum.inl x)).subtype)) : ℤ)
      = (Nat.card P : ℤ) * (Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ'.comp P.subtype)) : ℤ) := by
    intro x
    have hcx : Nat.card ↥(G (Sum.inl x)) = Nat.card ↥P :=
      card_map_conjFSC P (x : F)
    have hdx : Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ'.comp (G (Sum.inl x)).subtype))
        = Module.finrank (ZMod q) ↥(Representation.invariants (ρ'.comp P.subtype)) :=
      hconj (x : F)
    rw [hcx, hdx]
    simp [nn, Sum.elim_inl]
  have hblock : (∑ x : ↥K, nn (Sum.inl x) * (Nat.card (G (Sum.inl x)) : ℤ) *
      (Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ'.comp (G (Sum.inl x)).subtype)) : ℤ))
      = (Nat.card K : ℤ) * ((Nat.card P : ℤ) * (Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ'.comp P.subtype)) : ℤ)) := by
    rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    simp [Nat.card_eq_fintype_card]
  have h3 : nn (Sum.inr 0) * (Nat.card (G (Sum.inr 0)) : ℤ) *
      (Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ'.comp (G (Sum.inr 0)).subtype)) : ℤ) = 0 := by
    rw [hG0, hn0, hinvK]
    simp
  have h4 : nn (Sum.inr 1) * (Nat.card (G (Sum.inr 1)) : ℤ) *
      (Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ'.comp (G (Sum.inr 1)).subtype)) : ℤ) = 0 := by
    rw [hG1, hn1, hinvTop]
    simp
  have h5 : nn (Sum.inr 2) * (Nat.card (G (Sum.inr 2)) : ℤ) *
      (Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ'.comp (G (Sum.inr 2)).subtype)) : ℤ)
      = -((Nat.card K : ℤ) * (Module.finrank (ZMod q) (Additive M) : ℤ)) := by
    rw [hG2, hn2, hinvBot, finrank_top]
    simp
  rw [Fintype.sum_sum_type, Fin.sum_univ_three, hblock, h3, h4, h5] at hlin
  -- hence `|P| · dim M^P = dim M`
  have hKD : (Nat.card K : ℤ) * ((Nat.card P : ℤ) * (Module.finrank (ZMod q)
      ↥(Representation.invariants (ρ'.comp P.subtype)) : ℤ)
        - (Module.finrank (ZMod q) (Additive M) : ℤ)) = 0 := by
    nlinarith [hlin]
  have hKne : (Nat.card K : ℤ) ≠ 0 := by
    have : 0 < Nat.card K := Nat.card_pos
    omega
  have hPd : (Nat.card P : ℤ) * (Module.finrank (ZMod q)
      ↥(Representation.invariants (ρ'.comp P.subtype)) : ℤ)
        = (Module.finrank (ZMod q) (Additive M) : ℤ) := by
    rcases mul_eq_zero.mp hKD with h | h
    · exact absurd h hKne
    · exact sub_eq_zero.mp h
  have hnat : Module.finrank (ZMod q) (Additive M)
      = Nat.card P * Module.finrank (ZMod q)
          ↥(Representation.invariants (ρ'.comp P.subtype)) := by
    have := hPd
    omega
  have hMP : Nat.card M = q ^ Module.finrank (ZMod q) (Additive M) := by
    rw [← card_fixedBy_botFSC ρ, hcard ⊥, hinvBot, finrank_top]
  have hcrux : Nat.card (fixedBy ρ P) ^ Nat.card P = Nat.card M := by
    calc Nat.card (fixedBy ρ P) ^ Nat.card P
        = (q ^ Module.finrank (ZMod q)
            ↥(Representation.invariants (ρ'.comp P.subtype))) ^ Nat.card P := by rw [hcard P]
      _ = q ^ (Module.finrank (ZMod q)
            ↥(Representation.invariants (ρ'.comp P.subtype)) * Nat.card P) := by rw [← pow_mul]
      _ = q ^ Module.finrank (ZMod q) (Additive M) := by rw [mul_comm, ← hnat]
      _ = Nat.card M := hMP.symm
  -- assemble
  have key : (Nat.card (fixedBy ρ P)) ^ (Nat.card P * Nat.card K) *
        (Nat.card (fixedBy ρ K)) ^ Nat.card K = (Nat.card M) ^ Nat.card K := by
    rw [hcardK, one_pow, mul_one, pow_mul, hcrux]
  have key2 : (Nat.card (fixedBy ρ ⊤)) ^ (Nat.card P * Nat.card K) *
        (Nat.card M) ^ Nat.card K = (Nat.card M) ^ Nat.card K := by
    rw [hcardTop, one_pow, one_mul]
  rw [key, key2]

/-- `F`-simple elementary-abelian case of Wielandt's counting formula; route: Clifford + Schur +
Hilbert 90, see `Submission/Work/BSLit/Wielandt/NOTE_fsimple_case.md`.
`hTI` gives `K ⊓ P = ⊥` and `C_K(P) = 1`; since `|P| = p` is prime, `P = ⟨σ⟩`.  `q ∤ |K|` so
`M|_K` is semisimple; decompose `M` into the isotypic components of the distinct irreducible
`K`-submodules.  Conjugation by `σ` permutes these components (`K ⊴ F`), and the sum over one
`σ`-orbit is `F`-stable, hence all of `M` (by `hsimple`).
* one orbit of size `p`: `M = ⊕_{i ∈ ℤ/p} M_i` with `σ M_i = M_{i+1}`; then
  `M^σ = {(x, σx, …, σ^{p-1}x) : x ∈ M_0}` and `dim M^σ = dim M / p` because `σ` is an
  isomorphism `M_i → M_{i+1}`.
* some `σ`-stable component: then it is `F`-stable, so `M` is `K`-irreducible by `hsimple`; Schur
  makes `D := End_{𝔽_q[K]}(M)` a finite division ring (hence a field) with `K ⊆ D^×`, and
  `D`-subspaces are `K`-invariant, so `dim_D M = 1` and `M ≅ D`; `σ` is `D`-semilinear,
  `σ(x) = τ(x)·c`, with `τ^p = 1` and `N_{D/D^τ}(c) = 1`.
  * `τ ≠ 1`: Hilbert 90 gives `x ≠ 0` with `σ x = x`; `M^σ = D^τ x` is 1-dimensional over `D^τ`,
    so `dim M^σ = [D^τ : 𝔽_q] = dim M / p`.
  * `τ = 1`: `φ(F) ⊆ D^×` is abelian; `C_K(σ) = 1` (from `hTI`) and `σ` acts coprimely on `K`, so
    `K = [K,σ]` (see `Submission/Work/Coprime/commutator_fixedPoints_sup.lean`), whence
    `φ(K) = [φ(K),φ(σ)] = 1` and `M^K = M`, contradicting `hCK`.
Finally `dim M = p·dim M^σ` gives `|C_M(P)|^p = |M|` (with `C_M(K) = C_M(F) = 1` by `hCK`/`hsup`). -/
theorem frobeniusFSimpleCase {F M : Type*} [Group F] [Fintype F] [CommGroup M] [Finite M]
    {q p : ℕ} [Fact q.Prime] (hexp : ∀ m : M, m ^ q = 1) (hp : p.Prime)
    (ρ : F →* MulAut M) (hq : ¬ q ∣ Nat.card F)
    (hsimple : ∀ N : Subgroup M, (∀ g : F, N.map (ρ g) = N) → N = ⊥ ∨ N = ⊤)
    (K P : Subgroup F) (hsup : K ⊔ P = ⊤) (hcardP : Nat.card P = p)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hTI : ∀ k ∈ K, k ≠ 1 → P ⊓ P.map (MulAut.conj k⁻¹).toMonoidHom = ⊥)
    (hCK : ∀ m : M, (∀ k ∈ K, (ρ k) m = m) → m = 1) :
    (Nat.card (fixedBy ρ P)) ^ (Nat.card P * Nat.card K) * (Nat.card (fixedBy ρ K)) ^ Nat.card K
      = (Nat.card (fixedBy ρ ⊤)) ^ (Nat.card P * Nat.card K) * (Nat.card M) ^ Nat.card K := by
  refine frobeniusFSimpleCase_aux hexp hp ρ hq hsimple K P hsup hcardP hnorm hTI hCK ?_
  intro V _ _ _ σ ι _ H n hrel
  exact hLin_wielandt σ hq H n hrel

end Work.BSLit.Wielandt

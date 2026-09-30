import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.K2Z.fieldHalf
import Submission.Work.Pi6.BOCK.bocksteinLES
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.EMFG.emHomologyFG
import Submission.Work.SSS.serreFGThreeForTwo
import Submission.Work.Pi6.EMM2.finiteType
import Submission.Work.Pi6.EMM2.hZeroFree
import Submission.Work.Pi6.EMZ.groupSubsingleton
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.StemsB.fg_abelian_decomposition
import Submission.Work.Pi6.EMZ.rankDual
import Submission.Work.Pi6.K2Z.fgAbelianDivisible
import Submission.Work.Pi6.K2Z.fgAbelianQuotCyclic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `K(ℤ,2)` homology through degree 9, from the field computations

For a range model `X` of `K(ℤ,2)` through degree `N ≥ 10`:
`H_{2k}(X;ℤ) ≅ ℤ` and `H_{2k+1}(X;ℤ) = 0` for `k ≤ 4`, and `H_n(X;ℤ)` is free for `n ≤ 8`.

The input is `Work.Pi6.K2Z.fieldHalf` (the field-coefficient cohomology of `X`, over *every* field),
which via Kronecker duality gives the field-coefficient *homology* dimensions, and the integral
Bockstein sequence `Work.Pi6.BOCK.bocksteinLES`, which turns the mod-`p` homology into the successive
quotients of the integral homology.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.K2Z

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## Duality: cohomology dimensions give homology dimensions -/

/-- Over a field the Kronecker pairing is an isomorphism
(`Work.Cohomology.kronH_bijective_field`), so a one-dimensional degree of the cohomology forces the
homology in that degree to be one-dimensional (`Subspace.dual_finrank_eq`). -/
private lemma fgp_finrank_HR {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] {n : ℕ}
    (h : Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 X n) = 1) :
    Module.finrank 𝕜 ↥(Work.Pi6.HR 𝕜 X n) = 1 := by
  have e : ↥(Work.Pi6.Coh 𝕜 X n) ≃ₗ[𝕜] (↥(Work.Pi6.HR 𝕜 X n) →ₗ[𝕜] 𝕜) :=
    LinearEquiv.ofBijective (Work.Cohomology.kronH 𝕜 (TopCat.toSSet.obj (TopCat.of X)) n)
      (Work.Cohomology.kronH_bijective_field 𝕜 (TopCat.toSSet.obj (TopCat.of X)) n)
  rw [← Subspace.dual_finrank_eq (K := 𝕜) (V := ↥(Work.Pi6.HR 𝕜 X n))]
  rw [← LinearEquiv.finrank_eq e]
  exact h

/-- Dually, a trivial degree of the cohomology forces the homology in that degree to vanish: the
dual of `H_n(X;𝕜)` is never smaller (`Work.Pi6.EMZ.rank_HR_le_rank_Coh`). -/
private lemma fgp_subsingleton_HR {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] {n : ℕ}
    (h : Subsingleton ↥(Work.Pi6.Coh 𝕜 X n)) : Subsingleton ↥(Work.Pi6.HR 𝕜 X n) := by
  have h0 : Module.rank 𝕜 ↥(Work.Pi6.Coh 𝕜 X n) = 0 := rank_zero_iff.mpr h
  have hle := Work.Pi6.EMZ.rank_HR_le_rank_Coh 𝕜 X n
  have hle0 : Module.rank 𝕜 ↥(Work.Pi6.HR 𝕜 X n) ≤ 0 := hle.trans_eq h0
  have hz : Module.rank 𝕜 ↥(Work.Pi6.HR 𝕜 X n) = 0 := le_antisymm hle0 bot_le
  exact rank_zero_iff.mp hz

/-- A one-dimensional `ℤ/p`-vector space is `ℤ/p` as an abelian group. -/
private lemma fgp_addEquivZMod (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (h : Module.finrank (ZMod p) V = 1) : Nonempty (V ≃+ ZMod p) := by
  obtain ⟨b⟩ := (finrank_eq_one_iff (K := ZMod p) (V := V) (Fin 1)).mp h
  exact ⟨b.equivFun.toAddEquiv.trans
    (LinearEquiv.funUnique (Fin 1) (ZMod p) (ZMod p)).toAddEquiv⟩

/-! ## The Bockstein quotient -/

/-- **The Bockstein reduction is onto when the next lower integral homology is torsion-free.**
Let `red : A →+ M` and `del : M →+ A'` be consecutive maps of the Bockstein sequence of a prime `p`,
with `M` a `ℤ/p`-module (so every element of `M` is killed by `p`) and `A'` `p`-torsion-free.  Then
`del = 0`, hence `red` is onto, and `A/pA ≅ M`. -/
private lemma fgp_quotIsoOfExact {p : ℕ} {A M A' : Type} [AddCommGroup A] [AddCommGroup M]
    [AddCommGroup A'] [Module (ZMod p) M] (red : A →+ M) (del : M →+ A')
    (h1 : Function.Exact (fun a : A => (p : ℤ) • a) red)
    (h2 : Function.Exact red del)
    (htor : ∀ a' : A', (p : ℤ) • a' = 0 → a' = 0) :
    Nonempty ((A ⧸ Work.Pi6.EMZ.pH p A) ≃+ M) := by
  have hdel0 : ∀ x : M, del x = 0 := by
    intro x
    refine htor (del x) ?_
    rw [← map_zsmul]
    have hpx : (p : ℤ) • x = 0 := by
      rw [← Int.cast_smul_eq_zsmul (ZMod p) p x]
      simp
    rw [hpx, map_zero]
  have htop : red.range = ⊤ := by
    ext y
    constructor
    · intro _
      exact AddSubgroup.mem_top y
    · intro _
      have h0 : y ∈ Set.range ⇑red := (h2 y).mp (hdel0 y)
      obtain ⟨x, hx⟩ := h0
      exact ⟨x, hx⟩
  have hker : red.ker = Work.Pi6.EMZ.pH p A := by
    ext a
    constructor
    · intro ha
      have h0 : red a = 0 := ha
      exact (h1 a).mp h0
    · intro ha
      obtain ⟨y, hy⟩ := Work.Pi6.EMZ.mem_pH.mp ha
      have h0 : red a = 0 := (h1 a).mpr ⟨y, hy⟩
      exact h0
  rw [← hker]
  refine ⟨(QuotientAddGroup.quotientKerEquivRange red).trans ?_⟩
  exact
    { toFun := fun x => x.1
      invFun := fun y => ⟨y, by rw [htop]; exact AddSubgroup.mem_top y⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl }

/-! ## The two group-theoretic inputs, in the form needed for the homology of `X`

`H_n(X;ℤ)` is a `ModuleCat ℤ`, so its `Module ℤ` structure is the one carried by the category, while
the statements of the group-theoretic lemmas use the canonical `ℤ`-module structure of an abelian
group.  The two are equal (`Work.Pi6.EMZ.moduleFinite_canonical`), and the wrappers below hide the
transport. -/

/-- `Module.Finite` transfers between any two `Module ℤ`-structures on the same abelian group. -/
private theorem fgp_moduleFinite_canonical {G : Type} [AddCommGroup G] (m : Module ℤ G)
    (h : @Module.Finite ℤ G _ _ m) :
    @Module.Finite ℤ G _ _ (AddCommGroup.toIntModule G) := by
  rw [Subsingleton.elim m (AddCommGroup.toIntModule G)] at h
  exact h

/-- A finitely generated abelian group with `A/pA ≅ ℤ/p` for every prime `p` is `ℤ`
(`Work.Pi6.K2Z.fgAbelianQuotCyclic`), in the form needed below. -/
private theorem fgp_quotCyclic (A : Type) [AddCommGroup A] (m : Module ℤ A)
    (h : @Module.Finite ℤ A _ _ m)
    (hq : ∀ p : ℕ, p.Prime → Nonempty ((A ⧸ Work.Pi6.EMZ.pH p A) ≃+ ZMod p)) :
    Nonempty (A ≃+ ℤ) :=
  @Work.Pi6.K2Z.fgAbelianQuotCyclic A _ (fgp_moduleFinite_canonical m h) hq

/-- A finitely generated abelian group divisible by every prime is trivial
(`Work.Pi6.K2Z.fgAbelianDivisible`), in the form needed below. -/
private theorem fgp_divisible (A : Type) [AddCommGroup A] (m : Module ℤ A)
    (h : @Module.Finite ℤ A _ _ m)
    (hq : ∀ p : ℕ, p.Prime → Subsingleton (A ⧸ Work.Pi6.EMZ.pH p A)) :
    Subsingleton A :=
  @Work.Pi6.K2Z.fgAbelianDivisible A _ (fgp_moduleFinite_canonical m h) hq

/-! ## The main theorem -/

theorem fgFromPrimes (hM : Work.Pi6.MSSHolds) (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ)
    (hN : 10 ≤ N) (hX : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N X x₀) :
    (∀ k : ℕ, k ≤ 4 → Nonempty (Work.Pi6.HR ℤ X (2 * k) ≅ ModuleCat.of ℤ ℤ)) ∧
    (∀ k : ℕ, k ≤ 4 → Subsingleton (Work.Pi6.HR ℤ X (2 * k + 1))) ∧
    (∀ n : ℕ, n ≤ 8 → Module.Free ℤ (Work.Pi6.HR ℤ X n)) := by
  classical
  -- ## The range and finite generation of the integral homology
  have hX10 : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 10 X x₀ :=
    Work.EMFG.isEMSpaceUpTo_mono hX (by omega)
  have hfg : ∀ i : ℕ, i ≤ 9 → Module.Finite ℤ (Work.Pi6.HR ℤ X i) := by
    have h' : Work.Serre.IsEMSpaceUpTo ℤ 2 (by omega) (9 + 1) X x₀ :=
      Work.EMFG.isEMSpaceUpTo_congr hX10
    exact Work.EMFG.emHomologyFG Work.SSS.serreFGThreeForTwo (A := ℤ) (m := 2)
      (hm := by norm_num) (N := 9) (X := X) (x := x₀) h'
  -- ## Kronecker duality: the field-coefficient homology dimensions
  have hfield : ∀ (𝕜 : Type) [Field 𝕜] (n : ℕ), n ≤ 9 →
      ((Even n → Module.finrank 𝕜 ↥(Work.Pi6.HR 𝕜 X n) = 1) ∧
        (Odd n → Subsingleton ↥(Work.Pi6.HR 𝕜 X n))) := by
    intro 𝕜 _ n _
    obtain ⟨w, hw⟩ := Work.Pi6.K2Z.fieldHalf hM X x₀ N hN hX 𝕜
    constructor
    · intro hev
      obtain ⟨k, hk'⟩ := hev
      have hk : k ≤ 4 := by omega
      have hn2 : n = 2 * k := by omega
      rw [hn2]
      exact fgp_finrank_HR (hw k hk).2.1
    · intro hod
      obtain ⟨k, hk'⟩ := hod
      have hk : k ≤ 4 := by omega
      have hn2 : n = 2 * k + 1 := by omega
      rw [hn2]
      exact fgp_subsingleton_HR (hw k hk).2.2
  -- ## Degree `0`
  have hpi0 : Subsingleton (HomotopyGroup (Fin 0) X x₀) :=
    hX.2 0 (by norm_num) (Or.inl (by norm_num))
  have h0iso : Nonempty (Work.Pi6.HR ℤ X 0 ≅ ModuleCat.of ℤ ℤ) := by
    haveI : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ hpi0
    have hI : IsIso ((TopCat.of X).singularHomology₀ε (C := ModuleCat ℤ) (ModuleCat.of ℤ ℤ)) :=
      inferInstance
    have hbij : Function.Bijective
        (⇑(((TopCat.of X).singularHomology₀ε (C := ModuleCat ℤ) (ModuleCat.of ℤ ℤ)).hom)) :=
      (ConcreteCategory.isIso_iff_bijective _).mp hI
    exact ⟨(LinearEquiv.ofBijective _ hbij).toModuleIso⟩
  -- ## The even step: `H_n(X;ℤ) = 0 ⟹ H_{n+1}(X;ℤ) ≅ ℤ`
  have evenStep : ∀ n : ℕ, Even (n + 1) → n + 1 ≤ 8 → Subsingleton ↥(Work.Pi6.HR ℤ X n) →
      Nonempty (Work.Pi6.HR ℤ X (n + 1) ≅ ModuleCat.of ℤ ℤ) := by
    intro n hn hn8 hsub
    have hquot : ∀ p : ℕ, p.Prime →
        Nonempty ((Work.Pi6.HR ℤ X (n + 1) ⧸
          Work.Pi6.EMZ.pH p (Work.Pi6.HR ℤ X (n + 1))) ≃+ ZMod p) := by
      intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      have htor : ∀ a' : Work.Pi6.HR ℤ X n, (p : ℤ) • a' = 0 → a' = 0 :=
        fun a' _ => Subsingleton.elim a' 0
      obtain ⟨red, del, h1, h2, _h3, _hn1, _hn2⟩ := Work.Pi6.BOCK.bocksteinLES p hp
      have h1' : Function.Exact (fun a : Work.Pi6.HR ℤ X (n + 1) => (p : ℤ) • a)
          (⇑(red (X := X) (n + 1))) := h1 (X := X) (n + 1)
      have h2' : Function.Exact (⇑(red (X := X) (n + 1))) (⇑(del (X := X) n)) :=
        h2 (X := X) n
      obtain ⟨e1⟩ := fgp_quotIsoOfExact (red (X := X) (n + 1)) (del (X := X) n) h1' h2' htor
      have hfin : Module.finrank (ZMod p) ↥(Work.Pi6.HR (ZMod p) X (n + 1)) = 1 :=
        (hfield (ZMod p) (n + 1) (by omega)).1 hn
      obtain ⟨e2⟩ := fgp_addEquivZMod p (↥(Work.Pi6.HR (ZMod p) X (n + 1))) hfin
      exact ⟨e1.trans e2⟩
    obtain ⟨e⟩ := fgp_quotCyclic (↥(Work.Pi6.HR ℤ X (n + 1))) (Work.Pi6.HR ℤ X (n + 1)).isModule
      (hfg (n + 1) (by omega)) hquot
    exact ⟨e.toIntLinearEquiv.toModuleIso⟩
  -- ## The odd step: `H_n(X;ℤ) ≅ ℤ ⟹ H_{n+1}(X;ℤ) = 0`
  have oddStep : ∀ n : ℕ, Odd (n + 1) → n + 1 ≤ 9 →
      Nonempty (Work.Pi6.HR ℤ X n ≅ ModuleCat.of ℤ ℤ) →
      Subsingleton ↥(Work.Pi6.HR ℤ X (n + 1)) := by
    intro n hn hn9 heven
    have htorm : ∀ (p : ℕ), p.Prime → ∀ a' : Work.Pi6.HR ℤ X n,
        (p : ℤ) • a' = 0 → a' = 0 := by
      intro p hp a' ha'
      have e : ↥(Work.Pi6.HR ℤ X n) ≃+ ℤ := heven.some.toLinearEquiv.toAddEquiv
      have h1 : (p : ℤ) • e a' = 0 := by rw [← map_zsmul, ha', map_zero]
      have h2 : (p : ℤ) * e a' = 0 := by simpa [zsmul_eq_mul] using h1
      have h3 : e a' = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h (by exact_mod_cast hp.ne_zero)
        · exact h
      exact e.injective (by rw [h3, map_zero])
    have hquot : ∀ p : ℕ, p.Prime → Subsingleton (Work.Pi6.HR ℤ X (n + 1) ⧸
        Work.Pi6.EMZ.pH p (Work.Pi6.HR ℤ X (n + 1))) := by
      intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨red, del, h1, h2, _h3, _hn1, _hn2⟩ := Work.Pi6.BOCK.bocksteinLES p hp
      have h1' : Function.Exact (fun a : Work.Pi6.HR ℤ X (n + 1) => (p : ℤ) • a)
          (⇑(red (X := X) (n + 1))) := h1 (X := X) (n + 1)
      have h2' : Function.Exact (⇑(red (X := X) (n + 1))) (⇑(del (X := X) n)) :=
        h2 (X := X) n
      obtain ⟨e1⟩ := fgp_quotIsoOfExact (red (X := X) (n + 1)) (del (X := X) n) h1' h2'
        (htorm p hp)
      have hMsub : Subsingleton ↥(Work.Pi6.HR (ZMod p) X (n + 1)) :=
        (hfield (ZMod p) (n + 1) (by omega)).2 hn
      haveI := hMsub
      exact e1.toEquiv.subsingleton
    exact fgp_divisible (↥(Work.Pi6.HR ℤ X (n + 1))) (Work.Pi6.HR ℤ X (n + 1)).isModule
      (hfg (n + 1) (by omega)) hquot
  -- ## The induction
  have key : ∀ k : ℕ, k ≤ 4 →
      Nonempty (Work.Pi6.HR ℤ X (2 * k) ≅ ModuleCat.of ℤ ℤ) ∧
      Subsingleton ↥(Work.Pi6.HR ℤ X (2 * k + 1)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have h₀ : Nonempty (Work.Pi6.HR ℤ X (2 * 0) ≅ ModuleCat.of ℤ ℤ) := h0iso
      refine ⟨h₀, ?_⟩
      have h₁ := oddStep 0 ⟨0, by norm_num⟩ (by norm_num) h₀
      simpa using h₁
    | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      have hev0 : Nonempty (Work.Pi6.HR ℤ X (2 * k + 1 + 1) ≅ ModuleCat.of ℤ ℤ) :=
        evenStep (2 * k + 1) ⟨k + 1, by omega⟩ (by omega) ihk.2
      have hev : Nonempty (Work.Pi6.HR ℤ X (2 * (k + 1)) ≅ ModuleCat.of ℤ ℤ) := by
        simpa [show 2 * k + 1 + 1 = 2 * (k + 1) from by omega] using hev0
      refine ⟨hev, ?_⟩
      exact oddStep (2 * (k + 1)) ⟨k + 1, by omega⟩ (by omega) hev
  refine ⟨fun k hk => (key k hk).1, fun k hk => (key k hk).2, ?_⟩
  -- ## Freeness through degree 8
  intro n hn
  rcases Nat.even_or_odd n with hev | hod
  · obtain ⟨k, hk'⟩ := hev
    have hk2 : n = 2 * k := by omega
    have hk4 : k ≤ 4 := by omega
    rw [hk2]
    exact Module.Free.of_equiv ((key k hk4).1.some.toLinearEquiv).symm
  · obtain ⟨k, hk'⟩ := hod
    have hk2 : n = 2 * k + 1 := by omega
    have hk4 : k ≤ 4 := by omega
    rw [hk2]
    haveI : Subsingleton ↥(Work.Pi6.HR ℤ X (2 * k + 1)) := (key k hk4).2
    infer_instance

end

end Work.Pi6.K2Z

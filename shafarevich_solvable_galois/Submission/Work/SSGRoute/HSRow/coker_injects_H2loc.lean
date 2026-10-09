import Mathlib
import Submission.Work.SSGRoute.HSConj
import Submission.Work.SSGRoute.HSRestrict
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.HS.Basic
import Submission.Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.PTCore.slice_mem_lcCocycles
import Submission.Work.PTCore.toClass_slice_mem_range_conj1
import Submission.Work.SSGRoute.HSTwoRow.procyclic_hypotheses
import Submission.Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp
import Submission.Work.SSGRoute.HSRow.exists_lcCocycles2_normalForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

private lemma toClass_smul_aux
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (r : ZMod p) {f : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K M I) :
    Work.SSGRoute.toClass p k Ω K M I (r • f)
      = r • Work.SSGRoute.toClass p k Ω K M I f := by
  have hrf : r • f ∈ Work.SSGRoute.lcCocycles p k Ω K M I := Submodule.smul_mem _ r hf
  rw [Work.SSGRoute.toClass, dif_pos hrf, Work.SSGRoute.toClass, dif_pos hf]
  rw [show (⟨r • f, hrf⟩ : ↥(Work.SSGRoute.lcCocycles p k Ω K M I)) = r • ⟨f, hf⟩
      from Subtype.ext rfl, map_smul]

private lemma toClass_sum_aux
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) {ι : Type*} (s : Finset ι) (c : ι → ZMod p)
    (f : ι → (Ω ≃ₐ[k] Ω) → M)
    (hf : ∀ i, f i ∈ Work.SSGRoute.lcCocycles p k Ω K M I) :
    Work.SSGRoute.toClass p k Ω K M I (∑ i ∈ s, c i • f i)
      = ∑ i ∈ s, c i • Work.SSGRoute.toClass p k Ω K M I (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      rw [Work.SSGRoute.toClass, dif_pos (Work.SSGRoute.lcCocycles p k Ω K M I).zero_mem]
      exact map_zero _
  | insert a s ha ih =>
      have ha' : c a • f a ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
        Submodule.smul_mem _ _ (hf a)
      have hs' : (∑ i ∈ s, c i • f i) ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
        Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hf i))
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Work.SSGRoute.toClass_add p k Ω K M I ha' hs',
        toClass_smul_aux p k Ω K M I (c a) (hf a), ih]

/-- The coinvariants `H¹_loc(I,M) ⧸ range (conj₁ - 1)` inject into `H²_loc(D_A,M)`, the second
half of the degree-`2` Hochschild–Serre two-row decomposition for `D_A = I ⋊ C`
(`C = closure (zpowers σ)`).  Verbatim copy of
`Submission/Work/SSGRoute/HSTwoRow/coker_injects_H2loc.lean` (a stalled `sorry`) in the namespace
`Work.SSGRoute.HSRow`.  Companion: `Work.SSGRoute.HSRow.transgression_injective`; consumer:
`HSTwoRow/finrank_H2loc_decomp.lean` (proved, conditional on the two halves), and through it the
`μ_p`-base case of local Tate duality and the local Euler characteristic.

Background: the proof plan is in the docstring of the original file and in
`HSTwoRow/PLAN_H2row.md` — represent a coinvariant class by a locally constant `1`-cocycle `x` on
`I`; choose a modulus `m = d·t` (`d` the order of the conjugation action on `H¹_loc(I,M)`, `p ∣ t`,
available from `hZ`) with `Σ_{i<m} conj₁^i x = 0`; define the strict crossed hom
`Ψ(σ̄^j) = Σ_{i<j} conj₁^i x` on `C`; lift its values to locally constant `1`-cocycles, killing the
successive obstructions with `hvan` (`H²_loc(I,M) = 0`); the locally constant `2`-cocycle
`F(g,h) = p(g) • Ψ(p(h))(p(g)⁻¹ q(g) p(g))`, plus the `M`-valued corrections from
`isCoboundary2On_top_of_procyclicGrowth`, realises the class; injectivity because the construction
is a section of the transgression (or directly, by the gauge argument of the original file —
decide which, but do not leave the proof dependent on a sibling `sorry`).
Proved degree-`1` analogues: `HSTwoRow/finrank_H1loc_decomp.lean` (`exists_extension_cocycle`,
`Psi_eq_zero`); procyclic bookkeeping: `HSTwoRow/exists_zmodN_cocycle.lean`,
`HSTwoRow/exists_lcCocycleOn_zpowers_gen_eq.lean`, `HSTwoRow/toClass_eq_of_eq_on_gen.lean`;
continuity of the coordinates: `HSRow/Coords.lean`. -/
theorem coker_injects_H2loc
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω)))
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →*
        Multiplicative (ZMod n), Function.Surjective f)
    (hvan : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subsingleton (Work.SSGRoute.H2loc p k Ω K M I))
    (hfin : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I) :
    ∃ δ : (Work.SSGRoute.H1loc p k Ω K M I ⧸
          LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) →ₗ[ZMod p]
        Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A),
      Function.Injective δ
    := by
  classical
  haveI hFinI : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I) := hfin M
  let T : Work.SSGRoute.H1loc p k Ω K M I →ₗ[ZMod p] Work.SSGRoute.H1loc p k Ω K M I :=
    Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id
  haveI hFinQ : Module.Finite (ZMod p)
      (Work.SSGRoute.H1loc p k Ω K M I ⧸ LinearMap.range T) :=
    Module.Finite.of_surjective (Submodule.mkQ (LinearMap.range T))
      (Submodule.mkQ_surjective _)
  haveI hFreeQ : Module.Free (ZMod p)
      (Work.SSGRoute.H1loc p k Ω K M I ⧸ LinearMap.range T) :=
    Module.Free.of_divisionRing _ _
  let e := Module.finBasis (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I ⧸ LinearMap.range T)
  have hex : ∀ i : Fin (Module.finrank (ZMod p)
        (Work.SSGRoute.H1loc p k Ω K M I ⧸ LinearMap.range T)),
      ∃ (b : (Ω ≃ₐ[k] Ω) → M) (F : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M),
        b ∈ Work.SSGRoute.lcCocycles p k Ω K M I ∧
        F ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A) ∧
        (∀ g ∈ SSGRoute.decomp k A, ∀ n ∈ I, F g n = 0) ∧
        Work.SSGRoute.toClass p k Ω K M I (fun n => F n σ)
          = Work.SSGRoute.toClass p k Ω K M I b ∧
        Submodule.mkQ (LinearMap.range T) (Work.SSGRoute.toClass p k Ω K M I b) = e i := by
    intro i
    obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (LinearMap.range T) (e i)
    obtain ⟨b, hb, hbc⟩ := Work.SSGRoute.toClass_surjective p k Ω K M I y
    obtain ⟨F, hF, hFn, hFs⟩ :=
      exists_lcCocycles2_normalForm p k Ω K A I σ hI hIclosed hnorm hσ hsup hinf hZ hvan
        hfin M b hb
    exact ⟨b, F, hb, hF, hFn, hFs, by rw [hbc]; exact hy⟩
  choose b F hbmem hFmem hFn hFs hbq using hex
  let v : Fin (Module.finrank (ZMod p)
        (Work.SSGRoute.H1loc p k Ω K M I ⧸ LinearMap.range T)) →
      Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A) := fun i =>
    Submodule.mkQ (Submodule.comap
        (Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A)).subtype
        (Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A)))
      ⟨F i, hFmem i⟩
  refine ⟨e.constr (ZMod p) v, ?_⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  set c : Fin (Module.finrank (ZMod p)
      (Work.SSGRoute.H1loc p k Ω K M I ⧸ LinearMap.range T)) → ZMod p :=
    fun i => (e.repr x) i with hc
  let G : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M := ∑ i, c i • F i
  have hGmem : G ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A) :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hFmem i))
  have hGn : ∀ g ∈ SSGRoute.decomp k A, ∀ n ∈ I, G g n = 0 := by
    intro g hg n hn
    simp only [G, Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i _ => by simp [hFn i g hg n hn])
  have hx' : (∑ i, c i • v i) = 0 := by
    have hthis := hx
    rw [Module.Basis.constr_apply] at hthis
    rw [Finsupp.sum_fintype (e.repr x) (fun b a => a • v b) (fun i => zero_smul _ _)] at hthis
    rwa [show (∑ i, (e.repr x) i • v i) = ∑ i, c i • v i from by rw [hc]] at hthis
  have hGclass : Submodule.mkQ (Submodule.comap
      (Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A)).subtype
      (Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A)))
      (⟨G, hGmem⟩ : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A))) = 0 := by
    have h1 : (⟨G, hGmem⟩ : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A)))
        = ∑ i, c i • (⟨F i, hFmem i⟩ :
            ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A))) := by
      apply Subtype.ext
      funext g h
      simp [G, Finset.sum_apply]
    rw [h1, map_sum]
    have h2 : ∀ i, Submodule.mkQ (Submodule.comap
        (Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A)).subtype
        (Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A)))
        (c i • (⟨F i, hFmem i⟩ :
          ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A)))) = c i • v i := by
      intro i; rw [map_smul]
    rw [Finset.sum_congr rfl (fun i _ => h2 i), hx']
  have hGcob : G ∈ Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A) := by
    have h := (Submodule.Quotient.mk_eq_zero (Submodule.comap
      (Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A)).subtype
      (Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A)))).mp hGclass
    exact h
  have hslice : ∀ i, (fun n => F i n σ) ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
    fun i => Work.PTCore.slice_mem_lcCocycles p k Ω K A I σ hI hσ hnorm2 M (F i) (hFmem i)
      (fun g hg n hn => hFn i g hg n hn)
  have hsliceG : (fun n => G n σ) ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
    Work.PTCore.slice_mem_lcCocycles p k Ω K A I σ hI hσ hnorm2 M G hGmem hGn
  have hrange : Work.SSGRoute.toClass p k Ω K M I (fun n => G n σ) ∈ LinearMap.range T :=
    Work.PTCore.toClass_slice_mem_range_conj1 p k Ω K A I σ hI hσ hnorm1 hnorm2 M G hGmem hGn
      hsliceG hGcob
  have hGs : (fun n => G n σ) = ∑ i, c i • (fun n => F i n σ) := by
    ext n
    simp [G, Finset.sum_apply]
  have hval : Work.SSGRoute.toClass p k Ω K M I (fun n => G n σ)
      = ∑ i, c i • Work.SSGRoute.toClass p k Ω K M I (fun n => F i n σ) := by
    rw [hGs, toClass_sum_aux p k Ω K M I Finset.univ c (fun i n => F i n σ)
      (fun i => hslice i)]
  have hval2 : ∑ i, c i • Work.SSGRoute.toClass p k Ω K M I (fun n => F i n σ)
      = ∑ i, c i • Work.SSGRoute.toClass p k Ω K M I (b i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hFs i]
  have hmem : (∑ i, c i • Work.SSGRoute.toClass p k Ω K M I (b i)) ∈ LinearMap.range T := by
    rw [← hval2, ← hval]; exact hrange
  have hzero : Submodule.mkQ (LinearMap.range T)
      (∑ i, c i • Work.SSGRoute.toClass p k Ω K M I (b i)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hmem
  have hxeq : Submodule.mkQ (LinearMap.range T)
      (∑ i, c i • Work.SSGRoute.toClass p k Ω K M I (b i)) = x := by
    have h3 : ∀ i, Submodule.mkQ (LinearMap.range T)
        (c i • Work.SSGRoute.toClass p k Ω K M I (b i)) = c i • e i := by
      intro i; rw [map_smul, hbq i]
    rw [map_sum, Finset.sum_congr rfl (fun i _ => h3 i), ← e.sum_repr x]
  rw [← hxeq, hzero]

end Work.SSGRoute.HSRow

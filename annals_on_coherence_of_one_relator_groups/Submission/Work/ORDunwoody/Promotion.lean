/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# JL Theorem 4.4, the descent step: `FP2TreePromotion` from the N12 services

This file proves the descent step of JL Theorem 4.4 from the services of node N12: the
quotient-tree construction of Serre §5 together with the partial subdivision of a tree (both
bundled in `QuotientTreeByNormalClosureOfElliptic`) and the freeness criteria
(`FreeOnTreeIsFree`).

Let `π : H ↠ G` have `ker π^{ab} ⊗ k = 0`, let `S'` be a cocompact `H`-tree with finitely
generated stabilizers which `π`-dominates a cocompact `G`-tree `T` through a domination map
`f₂`, and put `N = ker π`.  One chooses an `H`-invariant set `R` of edges of `S'`, subdivides
exactly those edges to get the tree `S₁`, takes vertex-orbit representatives `A` of `S₁` and
sets `K = ⟪⋃_{z ∈ A} (N ∩ (S₁)_z)⟫`.  By Serre §5 the quotient `S = S₁/K` is a tree for
`Q = H/K` with vertex stabilizers the images of those of `S₁`; the image `N_Q` of `N` in `Q`
acts on `S` with trivial vertex stabilizers, hence is free, and `(N_Q)^{ab} ⊗ k = 0` forces
`N_Q = 1`, i.e. `K = N` and `Q = G`.

The choice of `R` is where the correction to JL's proof lies.  JL take `S₁ = S'`.  A group
acting on a tree with trivial vertex stabilizers is only a free product of copies of `ℤ/2` and
a free group: an element that *inverts* an edge has no fixed vertex, is not absorbed by `K`,
and its image in `N_Q` is an involution — which for `k` with `2` invertible (`k = ℚ`!) the
tensor condition does not rule out.  Here `R` is the set of edges that `f₂` *collapses*:

* no element of `N` maps a vertex of `S₁` to an adjacent vertex (`hstep`): if `n ∈ N` did, say
  `n • u = w` with `S₁.Adj u w`, then `f₂ u = f₂(n • u) = f₂ w`, so the edge `{u,w}` of `S'` is
  collapsed by `f₂` and hence was subdivided — it is not an edge of `S₁`;
* the domination map still exists: on the midpoint of a subdivided edge it takes the value `f₂`
  of either endpoint, well defined precisely because `f₂` collapses that edge, while edges that
  `f₂` does *not* collapse are not subdivided.  (Subdividing an uncollapsed edge would be
  impossible: a midpoint of an edge that some `h ∈ H` inverts while `f₂` does not collapse it
  would have to be mapped to a `π h`-fixed vertex of `T`, and `π h` swaps the two distinct
  images of that edge's endpoints.)

Since edges of `S'` inverted by `N` are collapsed by `f₂` (as `N = ker π`), `N` inverts no
edge of `S₁`; and every edge of `S` lifts to an edge of `S₁` (`lift`) whose endpoints realise
any fibre (`fibre`), so `hstep` shows that `N_Q` acts on `S` without inversions.  Hence `N_Q`
is free by the first freeness criterion, and the tensor condition makes it trivial.
-/
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORDunwoody.Lemmas.isCocompact_iff_transversal
import Submission.Work.ORDunwoody.Lemmas.pullback_isCocompact
import Submission.Work.ORDunwoody.Lemmas.pullback_vertexStab
import Submission.Work.ORDunwoody.Lemmas.pullback_hasFGStab_of_bijective
import Submission.Work.ORDunwoody.Lemmas.abelianizationTensorVanishes_of_surjective
import Submission.Work.ORDunwoody.Lemmas.abelianizationTensorVanishes_of_mulEquiv
import Submission.Work.ORDunwoody.Lemmas.subsingleton_of_abelianizationTensorVanishes_freeGroup
import Submission.Work.ORDunwoody.Lemmas.barycentricDefs

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open GTree

/-- The `H`-invariant set of edges of `S'` that the domination map `f₂` collapses.  These are
exactly the edges that can be inverted by an element of `ker π`; they are the edges that are
subdivided in the corrected descent step. -/
noncomputable def collapseEdges {H : Type u} [Group H] {W : Type u} [MulAction H W]
    {G : Type u} [Group G] {V : Type u} [MulAction G V] (π : H →* G) (S' : GTree H W)
    (f₂ : W → V) (hf : ∀ (h : H) (u : W), f₂ (h • u) = π h • f₂ u) : EdgeInv H W :=
  { tree := S'
    edges := {e | e ∈ S'.graph.edgeSet ∧ ∀ u ∈ e, ∀ v ∈ e, f₂ u = f₂ v}
    isEdge := fun _ he => he.1
    smul_mem := by
      intro g e he
      refine ⟨?_, ?_⟩
      · revert he
        induction e using Sym2.ind with
        | _ u v =>
          intro he
          have huv : S'.Adj u v :=
            (SimpleGraph.mem_edgeSet (G := S'.graph) (v := u) (w := v)).mp he.1
          rw [Sym2.map_mk]
          exact (SimpleGraph.mem_edgeSet (G := S'.graph) (v := g • u) (w := g • v)).mpr
            (S'.smul_adj g huv)
      · intro a ha b hb
        rw [Sym2.mem_map] at ha hb
        obtain ⟨a₀, ha₀, rfl⟩ := ha
        obtain ⟨b₀, hb₀, rfl⟩ := hb
        rw [hf g a₀, hf g b₀, he.2 a₀ ha₀ b₀ hb₀] }

/-- **The descent step of JL Theorem 4.4**, from the services of node N12. -/
theorem fp2TreePromotion_of_services {k : Type u} [CommRing k] [Nontrivial k]
    (hQ : QuotientTreeByNormalClosureOfElliptic k) (hFree : FreeOnTreeIsFree k) :
    FP2TreePromotion k := by
  obtain ⟨hSerre, hSub⟩ := hQ
  obtain ⟨hFree1, _hFree2⟩ := hFree
  intro G _ H _ π hπ hker V _ T hT W _ S' hS'c hS'fg hdom
  classical
  obtain ⟨f₂⟩ := hdom
  -- ## Step 1: the `H`-invariant set `R` of edges of `S'` collapsed by `f₂`
  have hf₂_ker : ∀ (n : H), n ∈ π.ker → ∀ u : W, f₂ (n • u) = f₂ u := by
    intro n hn u
    rw [DominationMapOver.map_smul, MonoidHom.mem_ker.mp hn, one_smul]
  let R : EdgeInv H W :=
    collapseEdges π S' f₂ (fun h u => DominationMapOver.map_smul f₂ h u)
  have hR_const : ∀ (e : Sym2 W) (he : e ∈ R.edges) (u : W), u ∈ e →
      ∀ v : W, v ∈ e → f₂ u = f₂ v := by
    intro e he u hu v hv
    exact he.2 u hu v hv
  -- the defining property of `R` on a genuine edge
  have hR_spec : ∀ {u v : W}, S'.Adj u v → (s(u, v) ∈ R.edges ↔ f₂ u = f₂ v) := by
    intro u v huv
    constructor
    · intro h
      exact h.2 u (Sym2.mem_mk_left u v) v (Sym2.mem_mk_right u v)
    · intro h
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.mem_edgeSet]; exact huv
      intro a ha b hb
      rw [Sym2.mem_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [h]
  -- ## Step 2: the partial subdivision `S₁`
  obtain ⟨S₁, hS₁inl, hS₁inr, hS₁inrinr, hS₁sinl, hS₁sinr, _hS₁stab_inl, _hS₁stab_inr,
    hS₁c, hS₁fg⟩ := hSub H W R hS'c hS'fg
  -- ## Step 3: a transversal `A` of the vertex orbits of `S₁`
  obtain ⟨A, hA⟩ := (Lemmas.isCocompact_iff_transversal S₁).mp hS₁c |>.1
  -- ## Step 4: the subgroup `K`
  let Nsub : ∀ z : PSubV R, z ∈ A → Subgroup H := fun z _ => π.ker ⊓ S₁.vertexStab z
  have hN : ∀ (z : PSubV R) (hz : z ∈ A), Nsub z hz ≤ S₁.vertexStab z :=
    fun _ _ => inf_le_right
  let K : Subgroup H :=
    Subgroup.normalClosure (⋃ (z : PSubV R) (hz : z ∈ A), (Nsub z hz : Set H))
  have hKeq : K = Subgroup.normalClosure
      (⋃ (z : PSubV R) (hz : z ∈ A), (Nsub z hz : Set H)) := rfl
  haveI hKnormal : K.Normal := hKeq.symm ▸ Subgroup.normalClosure_normal
  -- ## Step 5: the quotient tree `S = S₁/K`, by Serre §5
  obtain ⟨X, instX, S, g, hg, hSc, hSfg, heq, hlift, hfib, hstab⟩ :=
    hSerre H S₁ A Nsub hN hA K hKeq hS₁c hS₁fg
  letI : MulAction (H ⧸ K) X := instX
  -- ## Step 6: `K ≤ ker π`
  have hKle : K ≤ π.ker := by
    rw [hKeq]
    refine Subgroup.normalClosure_le_normal ?_
    rintro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    exact (inf_le_left : Nsub w hw ≤ π.ker) hxw
  -- ## Step 7: the image `N_Q` of `ker π` in the quotient
  let NQ : Subgroup (H ⧸ K) := (π.ker).map (QuotientGroup.mk' K)
  letI : MulAction ↥NQ X := MulAction.compHom X NQ.subtype
  have hcompatN : ∀ (a : ↥NQ) (x : X), a • x = NQ.subtype a • x := fun _ _ => rfl
  -- ## Step 8: no element of `ker π` maps a vertex of `S₁` to an adjacent vertex
  have hstep : ∀ (n : H), n ∈ π.ker → ∀ (a b : PSubV R), S₁.Adj a b → n • a ≠ b := by
    intro n hn a b hab hnab
    rcases a with u | e <;> rcases b with v | f
    · -- old vertex to old vertex
      rw [hS₁inl] at hab
      obtain ⟨huv, hnotR⟩ := hab
      rw [hS₁sinl] at hnab
      have hnuv : n • u = v := Sum.inl.inj hnab
      have hc : f₂ u = f₂ v := by rw [← hnuv, hf₂_ker n hn u]
      exact hnotR ((hR_spec huv).mpr hc)
    · -- old vertex to midpoint: `inl` is not `inr`
      rw [hS₁sinl] at hnab
      exact absurd hnab (by simp)
    · -- midpoint to old vertex: `inr` is not `inl`
      obtain ⟨e', he'⟩ := hS₁sinr n e
      rw [he'] at hnab
      exact absurd hnab (by simp)
    · -- no two midpoints are adjacent
      exact absurd hab (hS₁inrinr e f)
  -- ## Step 9: the vertex stabilizers of `N_Q` on `S` are trivial
  have hfreepoint : ∀ x : X, S.vertexStab x ⊓ NQ = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    obtain ⟨hq1, hq2⟩ := Subgroup.mem_inf.mp hq
    rw [hstab x] at hq1
    obtain ⟨b, hb, hbq⟩ := Subgroup.mem_map.mp hq1
    obtain ⟨a, ha, haq⟩ := Subgroup.mem_map.mp hq2
    have hbK : b ∈ K := by
      have hab : a⁻¹ * b ∈ K := by
        have h1 : QuotientGroup.mk' K (a⁻¹ * b) = 1 := by
          rw [map_mul, map_inv, haq, hbq, inv_mul_cancel]
        have h2 : a⁻¹ * b ∈ (QuotientGroup.mk' K).ker := MonoidHom.mem_ker.mpr h1
        rwa [QuotientGroup.ker_mk'] at h2
      have hbker : b ∈ π.ker := by
        have h1 : π (a⁻¹ * b) = 1 := hKle hab
        have ha1 : π a = 1 := MonoidHom.mem_ker.mp ha
        rw [map_mul, map_inv, ha1, inv_one, one_mul] at h1
        simpa using h1
      -- conjugate `b` into the stabilizer of a vertex of `A`
      obtain ⟨h0, hh0⟩ := hA (Function.surjInv hg x)
      have hconj : h0 * b * h0⁻¹ ∈ S₁.vertexStab (h0 • Function.surjInv hg x) := by
        rw [GTree.vertexStab, MulAction.mem_stabilizer_iff]
        have hb' : b • Function.surjInv hg x = Function.surjInv hg x := hb
        show (h0 * b * h0⁻¹) • (h0 • Function.surjInv hg x) = h0 • Function.surjInv hg x
        rw [mul_smul, mul_smul, inv_smul_smul, hb']
      have hconjker : h0 * b * h0⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker] at hbker ⊢
        rw [map_mul, map_mul, map_inv, hbker, mul_one, mul_inv_cancel]
      have hinN : h0 * b * h0⁻¹ ∈ Nsub (h0 • Function.surjInv hg x) hh0 :=
        Subgroup.mem_inf.mpr ⟨hconjker, hconj⟩
      have hinK : h0 * b * h0⁻¹ ∈ K := by
        rw [hKeq]
        exact Subgroup.subset_normalClosure (Set.mem_iUnion.mpr ⟨h0 • Function.surjInv hg x,
          Set.mem_iUnion.mpr ⟨hh0, hinN⟩⟩)
      have hconj2 := hKnormal.conj_mem (h0 * b * h0⁻¹) hinK h0⁻¹
      have hEq : h0⁻¹ * (h0 * b * h0⁻¹) * h0⁻¹⁻¹ = b := by group
      rwa [hEq] at hconj2
    rw [← hbq]
    have h1 : QuotientGroup.mk' K b = 1 := by
      have h2 : b ∈ (QuotientGroup.mk' K).ker := by rwa [QuotientGroup.ker_mk']
      exact MonoidHom.mem_ker.mp h2
    exact h1
  have htriv : ∀ x : X, (S.pullback NQ.subtype hcompatN).vertexStab x = ⊥ := by
    intro x
    rw [Lemmas.pullback_vertexStab, eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_comap] at ha
    have h1 : (a : H ⧸ K) ∈ S.vertexStab x ⊓ NQ := Subgroup.mem_inf.mpr ⟨ha, a.2⟩
    rw [hfreepoint x, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  -- ## Step 10: `N_Q` acts on `S` without inversions
  have hnoInv : ∀ (a : ↥NQ) ⦃x y : X⦄, S.Adj x y → a • x = y → a • y = x → a = 1 := by
    intro a x y hxy hax _hay
    obtain ⟨p, q, hpq, hgp, hgq⟩ := hlift hxy
    obtain ⟨n, hn, hnq⟩ := Subgroup.mem_map.mp a.2
    have hgn : g (n • p) = g q := by
      rw [heq n p, hnq, hgp]
      exact hax.trans hgq.symm
    obtain ⟨k, hk⟩ := (hfib (n • p) q).mp hgn
    have hmem : (k : H) * n ∈ π.ker := Subgroup.mul_mem _ (hKle k.2) hn
    have hkq : ((k : H) * n) • p = q := by rw [mul_smul]; exact hk
    exact absurd hkq (hstep ((k : H) * n) hmem p q hpq)
  -- ## Step 11: `N_Q` is free
  have hfreeN : ∃ (α : Type u), Nonempty (↥NQ ≃* FreeGroup α) :=
    hFree1 ↥NQ (S.pullback NQ.subtype hcompatN) htriv hnoInv
  -- ## Step 12: `(N_Q)^{ab} ⊗ k = 0`
  have hNQker : AbelianizationTensorVanishes k ↥NQ := by
    let φ : ↥(π.ker) →* ↥NQ :=
      { toFun := fun a => ⟨QuotientGroup.mk' K (a : H), Subgroup.mem_map.mpr ⟨(a : H), a.2, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp }
    have hφ : Function.Surjective φ := by
      rintro ⟨q, hq⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
      exact ⟨⟨a, ha⟩, rfl⟩
    exact Lemmas.abelianizationTensorVanishes_of_surjective φ hφ hker
  -- ## Step 13: `N_Q` is trivial
  have hNQbot : NQ = ⊥ := by
    obtain ⟨α, ⟨e⟩⟩ := hfreeN
    have h1 : AbelianizationTensorVanishes k (FreeGroup α) :=
      Lemmas.abelianizationTensorVanishes_of_mulEquiv hNQker e
    have h2 : Subsingleton (FreeGroup α) :=
      Lemmas.subsingleton_of_abelianizationTensorVanishes_freeGroup α h1
    have hsub : Subsingleton ↥NQ := ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
    refine le_antisymm (fun q hq => ?_) bot_le
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hsub.elim (⟨q, hq⟩ : ↥NQ) 1))
  -- ## Step 14: `K = ker π`
  have hker_le_K : π.ker ≤ K := by
    intro a ha
    have h1 : QuotientGroup.mk' K a ∈ NQ := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    rw [hNQbot] at h1
    have h2 : QuotientGroup.mk' K a = 1 := Subgroup.mem_bot.mp h1
    have h3 : a ∈ (QuotientGroup.mk' K).ker := MonoidHom.mem_ker.mpr h2
    rwa [QuotientGroup.ker_mk'] at h3
  have hKker : K = π.ker := le_antisymm hKle hker_le_K
  -- ## Step 15: the isomorphism `H ⧸ K ≃* G`
  let e : (H ⧸ K) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hKker).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he_mk : ∀ h : H, e (QuotientGroup.mk' K h) = π h := by
    intro h
    show (QuotientGroup.quotientKerEquivOfSurjective π hπ)
      ((QuotientGroup.quotientMulEquivOfEq hKker) (QuotientGroup.mk' K h)) = π h
    rw [QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    exact QuotientGroup.kerLift_mk (φ := π) h
  -- ## Step 16: the domination map, through the partial subdivision
  have hRwt : ∀ e : {e : Sym2 W // e ∈ R.edges}, ∃ w : W, w ∈ (e : Sym2 W) :=
    fun e => Lemmas.exists_mem_of_mem_edgeSet (G := S'.graph) (R.isEdge (e : Sym2 W) e.2)
  let F : PSubV R → V := fun z => match z with
    | Sum.inl u => f₂ u
    | Sum.inr e => f₂ (Classical.choose (hRwt e))
  have hF_inl : ∀ u : W, F (Sum.inl u) = f₂ u := fun _ => rfl
  have hF_inr : ∀ (e : {e : Sym2 W // e ∈ R.edges}) (u : W), u ∈ (e : Sym2 W) →
      F (Sum.inr e) = f₂ u := by
    intro e u hu
    have h1 : f₂ (Classical.choose (hRwt e)) = f₂ u :=
      hR_const (e : Sym2 W) e.2 _ (Classical.choose_spec (hRwt e)) _ hu
    simpa [F] using h1
  have hF_adj : ∀ ⦃z w : PSubV R⦄, S₁.Adj z w → T.Adj (F z) (F w) ∨ F z = F w := by
    intro z w hzw
    rcases z with u | e <;> rcases w with v | f
    · rw [hS₁inl] at hzw
      rcases f₂.map_adj hzw.1 with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · have hu : u ∈ (f : Sym2 W) := (hS₁inr u f).mp hzw
      exact Or.inr (hF_inr f u hu).symm
    · have hv : v ∈ (e : Sym2 W) := (hS₁inr v e).mp hzw.symm
      exact Or.inr (hF_inr e v hv)
    · exact absurd hzw (hS₁inrinr e f)
  have hF_equiv : ∀ (h : H) (z : PSubV R), F (h • z) = π h • F z := by
    intro h z
    rcases z with u | e
    · calc F (h • (Sum.inl u : PSubV R)) = F (Sum.inl (h • u)) := by rw [hS₁sinl]
        _ = f₂ (h • u) := hF_inl _
        _ = π h • f₂ u := DominationMapOver.map_smul f₂ h u
        _ = π h • F (Sum.inl u) := by rw [hF_inl u]
    · obtain ⟨e', he'⟩ := hS₁sinr h e
      have hu : Classical.choose (hRwt e) ∈ (e : Sym2 W) := Classical.choose_spec (hRwt e)
      have hadj : S₁.Adj (Sum.inl (Classical.choose (hRwt e))) (Sum.inr e) :=
        (hS₁inr (Classical.choose (hRwt e)) e).mpr hu
      have hadj' : S₁.Adj (h • Sum.inl (Classical.choose (hRwt e))) (h • Sum.inr e) :=
        S₁.smul_adj h hadj
      rw [he', hS₁sinl] at hadj'
      have hmem : h • Classical.choose (hRwt e) ∈ (e' : Sym2 W) := (hS₁inr _ e').mp hadj'
      calc F (h • (Sum.inr e : PSubV R)) = F (Sum.inr e') := by rw [he']
        _ = f₂ (h • Classical.choose (hRwt e)) := hF_inr e' _ hmem
        _ = π h • f₂ (Classical.choose (hRwt e)) :=
            DominationMapOver.map_smul f₂ h (Classical.choose (hRwt e))
        _ = π h • F (Sum.inr e) := by rw [hF_inr e _ hu]
  have hF_K : ∀ (k : K) (z : PSubV R), F ((k : H) • z) = F z := by
    intro k z
    rcases z with u | e
    · calc F ((k : H) • (Sum.inl u : PSubV R)) = F (Sum.inl ((k : H) • u)) := by rw [hS₁sinl]
        _ = f₂ ((k : H) • u) := hF_inl _
        _ = f₂ u := hf₂_ker (k : H) (hKle k.2) u
        _ = F (Sum.inl u) := (hF_inl u).symm
    · obtain ⟨e', he'⟩ := hS₁sinr (k : H) e
      have hu : Classical.choose (hRwt e) ∈ (e : Sym2 W) := Classical.choose_spec (hRwt e)
      have hadj : S₁.Adj (Sum.inl (Classical.choose (hRwt e))) (Sum.inr e) :=
        (hS₁inr (Classical.choose (hRwt e)) e).mpr hu
      have hadj' :
          S₁.Adj ((k : H) • Sum.inl (Classical.choose (hRwt e))) ((k : H) • Sum.inr e) :=
        S₁.smul_adj (k : H) hadj
      rw [he', hS₁sinl] at hadj'
      have hmem : (k : H) • Classical.choose (hRwt e) ∈ (e' : Sym2 W) := (hS₁inr _ e').mp hadj'
      calc F ((k : H) • (Sum.inr e : PSubV R)) = F (Sum.inr e') := by rw [he']
        _ = f₂ ((k : H) • Classical.choose (hRwt e)) := hF_inr e' _ hmem
        _ = f₂ (Classical.choose (hRwt e)) := hf₂_ker (k : H) (hKle k.2) _
        _ = F (Sum.inr e) := (hF_inr e _ hu).symm
  have hF_fib : ∀ u v : PSubV R, g u = g v → F u = F v := by
    intro u v huv
    obtain ⟨k, hk⟩ := (hfib u v).mp huv
    exact (hF_K k u).symm.trans (by rw [hk])
  let Fbar : X → V := fun x => F (Function.surjInv hg x)
  have hFbar_eq : ∀ u : PSubV R, Fbar (g u) = F u := by
    intro u
    exact hF_fib _ _ (Function.surjInv_eq hg (g u))
  have hFbar_adj : ∀ ⦃x y : X⦄, S.Adj x y → T.Adj (Fbar x) (Fbar y) ∨ Fbar x = Fbar y := by
    intro x y hxy
    obtain ⟨p, q, hpq, hgp, hgq⟩ := hlift hxy
    have h1 := hF_adj hpq
    rw [← hgp, ← hgq, hFbar_eq p, hFbar_eq q]
    exact h1
  -- ## Step 17: transport `S` to a `G`-tree along `e`
  let em : G →* (H ⧸ K) := e.symm.toMonoidHom
  letI : MulAction G X := MulAction.compHom X em
  have hcompatG : ∀ (g : G) (x : X), g • x = em g • x := fun _ _ => rfl
  refine ⟨X, inferInstance, S.pullback em hcompatG, ?_, ?_, ?_⟩
  · exact Lemmas.pullback_isCocompact em
      (fun q => ⟨e q, by simp [em]⟩) hcompatG S hSc
  · exact Lemmas.pullback_hasFGStab_of_bijective em
      ⟨fun a b h => e.symm.injective h, fun q => ⟨e q, by simp [em]⟩⟩ hcompatG S hSfg
  · refine ⟨{ toFun := Fbar, map_smul' := ?_, map_adj' := ?_ }⟩
    · intro γ x
      obtain ⟨h, hh⟩ : ∃ h : H, QuotientGroup.mk' K h = em γ :=
        QuotientGroup.mk'_surjective K (em γ)
      have hπh : π h = γ := by
        have h2 : e (em γ) = π h := by
          have h3 := he_mk h
          rw [hh] at h3
          exact h3
        rw [← h2]
        exact e.apply_symm_apply γ
      have hγx : γ • x = QuotientGroup.mk' K h • x := by
        rw [hh]
        exact hcompatG γ x
      have hfibx : g (Function.surjInv hg (QuotientGroup.mk' K h • x))
          = g (h • Function.surjInv hg x) := by
        rw [Function.surjInv_eq hg, heq h (Function.surjInv hg x), Function.surjInv_eq hg x]
      calc Fbar (γ • x) = Fbar (QuotientGroup.mk' K h • x) := by rw [hγx]
        _ = F (Function.surjInv hg (QuotientGroup.mk' K h • x)) := rfl
        _ = F (h • Function.surjInv hg x) := hF_fib _ _ hfibx
        _ = π h • F (Function.surjInv hg x) := hF_equiv h (Function.surjInv hg x)
        _ = γ • Fbar x := by rw [hπh]
    · intro x y hxy
      exact hFbar_adj hxy

end Work.ORDunwoody

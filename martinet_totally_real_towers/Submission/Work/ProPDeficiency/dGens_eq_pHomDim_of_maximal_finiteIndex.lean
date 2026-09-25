import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.HomRank
import Submission.Work.ProPDeficiency.pHomDim_le_dGens
import Submission.Work.ProPDeficiency.dGens_eq_pHomDim_of_isPGroup
import Submission.Commons.GroupTheory.PGroup.index_coatom_eq_prime
import Submission.Commons.GroupTheory.PGroup.frattini_eq_pow_sup_commutator
import Submission.Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le

namespace Work.ProPDeficiency

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

-- File: Submission/Work/ProPDeficiency/dGens_eq_pHomDim_of_maximal_finiteIndex.lean, namespace `Work.ProPDeficiency`.
-- The `d = dim H¹` identity for a finitely generated discrete "pro-p" group: if every finite
-- quotient of `G` is a `p`-group and every maximal subgroup of `G` has finite index (the discrete
-- substitute for "G is a finitely generated pro-p group"), then `pHomDim p G = dGens G`.
-- `dGens`, `IsGeneratingSet`, `dGens_le_of_surjective` are in `Submission.Work.ProPDeficiency.Basic`;
-- `HomFp`, `pHomDim` in `Submission.Work.ProPDeficiency.HomRank`.
--
-- The argument: let `K = (evalHom p G).ker` be the kernel of the evaluation map into the double
-- dual `(HomFp p G →* 𝔽_p)`; this is `⨅ φ, φ.ker`, so *every* homomorphism `G →* 𝔽_p` kills `K` and
-- `HomFp p G ≅ HomFp p (G ⧸ K)`.  Since `HomFp p G` is finite, `G ⧸ K` is finite, so `K` has
-- finite index and `hquot` makes `G ⧸ K` a finite `p`-group:
--   `pHomDim p G = pHomDim p (G ⧸ K) = dGens (G ⧸ K)`.
-- For the reverse inequality one lifts a minimal generating set of `G ⧸ K` to `G`; the lift
-- generates `G` because (the crux) `K ≤ frattini G`: for a maximal subgroup `M` (which has finite
-- index by `hmax`) the quotient `G ⧸ core M` is a finite `p`-group (`hquot`) in which the image of
-- `M` is maximal, hence normal of index `p`, giving a surjection `G →* 𝔽_p` whose kernel is `M`.
-- Then `frattini_nongenerating` finishes, using coatomicity of the subgroup lattice of a finitely
-- generated group.

/-! ## The evaluation homomorphism into the double dual -/

/-- Evaluation: an element `g` of `G` induces the homomorphism "evaluate at `g`" on the group
`HomFp p G = Hom(G, 𝔽_p)` of homomorphisms to `𝔽_p`. -/
noncomputable def evalHom (p : ℕ) (G : Type*) [Group G] :
    G →* (HomFp p G →* Multiplicative (ZMod p)) where
  toFun g :=
    { toFun := fun φ => φ g
      map_one' := by simp
      map_mul' := fun φ ψ => MonoidHom.mul_apply φ ψ g }
  map_one' := by ext φ; simp
  map_mul' := fun g h => by ext φ; exact map_mul φ g h

/-- An element of `G` lies in the kernel of the evaluation map (`= ⨅ φ, φ.ker`) iff it is killed by
every homomorphism `G →* 𝔽_p`. -/
theorem mem_evalHom_ker {p : ℕ} {G : Type*} [Group G] (g : G) :
    g ∈ (evalHom p G).ker ↔ ∀ φ : HomFp p G, φ g = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h φ
    exact DFunLike.congr_fun h φ
  · intro h
    exact MonoidHom.ext h

/-- Every homomorphism `G →* 𝔽_p` factors through `G ⧸ (evalHom p G).ker`. -/
theorem evalHom_ker_le_ker {p : ℕ} {G : Type*} [Group G] (φ : HomFp p G) :
    (evalHom p G).ker ≤ φ.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  exact (mem_evalHom_ker x).mp hx φ

/-! ## Finiteness of `Hom(G, 𝔽_p)` and of the quotient -/

/-- For a finitely generated group, `Hom(G, 𝔽_p)` is finite: a homomorphism is determined by its
values on a finite generating set. -/
theorem finite_homFp_of_fg {p : ℕ} [NeZero p] {G : Type*} [Group G] [Group.FG G] :
    Finite (HomFp p G) := by
  obtain ⟨n, ⟨P⟩⟩ := Group.fg_iff_nonempty_finite_generators.mp (inferInstance : Group.FG G)
  refine @Finite.of_injective _ _ ?_ (fun φ : HomFp p G => fun i : Fin n => φ (P.val i))
    (fun φ ψ h => P.hom_ext φ ψ (fun i => congr_fun h i))
  exact Pi.finite

/-- The kernel of the evaluation map has finite index: it is the kernel of a map into a finite
product of copies of `𝔽_p`. -/
theorem finite_quot_ker_eval {p : ℕ} [NeZero p] {G : Type*} [Group G] [Group.FG G] :
    Finite (G ⧸ (evalHom p G).ker) := by
  haveI : Finite (HomFp p G) := finite_homFp_of_fg
  haveI : Finite (HomFp p G →* Multiplicative (ZMod p)) := by
    refine @Finite.of_injective _ _ ?_ (fun f : HomFp p G →* Multiplicative (ZMod p) => ⇑f)
      (fun f g hfg => MonoidHom.ext fun φ => congrFun hfg φ)
    exact Pi.finite
  haveI : Finite ↥(evalHom p G).range :=
    Finite.of_injective
      (fun x : ↥(evalHom p G).range => (x : HomFp p G →* Multiplicative (ZMod p)))
      (fun x y h => Subtype.ext h)
  exact Finite.of_equiv ↥(evalHom p G).range
    (QuotientGroup.quotientKerEquivRange (evalHom p G)).symm

theorem finiteIndex_ker_eval {p : ℕ} [NeZero p] {G : Type*} [Group G] [Group.FG G] :
    (evalHom p G).ker.FiniteIndex :=
  Subgroup.finiteIndex_iff_finite_quotient.mpr (finite_quot_ker_eval (p := p) (G := G))

/-- Precomposition with the quotient map is a bijection
`HomFp p (G ⧸ K) ≃ HomFp p G` for `K = (evalHom p G).ker`, because every homomorphism to `𝔽_p`
kills `K`. -/
theorem natCard_homFp_quot_ker_eval {p : ℕ} {G : Type*} [Group G] :
    Nat.card (HomFp p (G ⧸ (evalHom p G).ker)) = Nat.card (HomFp p G) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun ψ : HomFp p (G ⧸ (evalHom p G).ker) => ψ.comp (QuotientGroup.mk' (evalHom p G).ker)) ?_)
  constructor
  · intro φ ψ h
    refine MonoidHom.ext fun y => ?_
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (evalHom p G).ker y
    have h' : φ ((QuotientGroup.mk' (evalHom p G).ker) x)
        = ψ ((QuotientGroup.mk' (evalHom p G).ker) x) := DFunLike.congr_fun h x
    rwa [hx] at h'
  · intro f
    exact ⟨QuotientGroup.lift (evalHom p G).ker f (evalHom_ker_le_ker f),
      QuotientGroup.lift_comp_mk' (evalHom p G).ker f (evalHom_ker_le_ker f)⟩

theorem pHomDim_quot_ker_eval {p : ℕ} {G : Type*} [Group G] :
    pHomDim p (G ⧸ (evalHom p G).ker) = pHomDim p G := by
  unfold pHomDim
  rw [natCard_homFp_quot_ker_eval]

/-! ## Maximal subgroups of a finitely generated group -/

/-- Every proper subgroup of a finitely generated group is contained in a maximal one: the
subgroup lattice of a finitely generated group is coatomic. -/
theorem isCoatomic_subgroup_of_fg {G : Type*} [Group G] [Group.FG G] :
    IsCoatomic (Subgroup G) := by
  classical
  obtain ⟨S, hS, -⟩ := exists_minimalGeneratingSet (G := G) (inferInstance : Group.FG G)
  refine IsCoatomic.of_isChain_bounded ?_
  intro c hc hne htop
  set s : Set G := ⋃ a ∈ c, (a : Set G) with hs
  have hmem : ∀ x : G, x ∈ s ↔ ∃ a : Subgroup G, a ∈ c ∧ x ∈ a := by
    intro x
    simp [hs]
  have hchain : ∀ a ∈ c, ∀ b ∈ c, a ≤ b ∨ b ≤ a := fun a ha b hb =>
    if h : a = b then Or.inl (le_of_eq h) else hc ha hb h
  have hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s := by
    intro x hx y hy
    obtain ⟨a, ha, hxa⟩ := (hmem x).mp hx
    obtain ⟨b, hb, hyb⟩ := (hmem y).mp hy
    rcases hchain a ha b hb with hab | hba
    · exact (hmem _).mpr ⟨b, hb, b.mul_mem (hab hxa) hyb⟩
    · exact (hmem _).mpr ⟨a, ha, a.mul_mem hxa (hba hyb)⟩
  have hone : (1 : G) ∈ s := by
    obtain ⟨a, ha⟩ := hne
    exact (hmem 1).mpr ⟨a, ha, a.one_mem⟩
  have hinv : ∀ x ∈ s, x⁻¹ ∈ s := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := (hmem x).mp hx
    exact (hmem _).mpr ⟨a, ha, a.inv_mem hxa⟩
  let U : Subgroup G :=
    { carrier := s, mul_mem' := fun ha hb => hmul _ ha _ hb, one_mem' := hone,
      inv_mem' := fun ha => hinv _ ha }
  have hmemU : ∀ x : G, x ∈ U ↔ x ∈ s := fun x => Iff.rfl
  have hle : U ∈ upperBounds c := fun a ha x hx => (hmem x).mpr ⟨a, ha, hx⟩
  have hUne : U ≠ ⊤ := by
    intro hUt
    have hSall : ∀ x ∈ S, x ∈ s := fun x hx => (hmemU x).mp (by rw [hUt]; exact Subgroup.mem_top x)
    have hex : ∃ a ∈ c, ∀ x ∈ S, x ∈ a := by
      have hmain : ∀ T : Finset G, (∀ x ∈ T, x ∈ s) → ∃ a ∈ c, ∀ x ∈ T, x ∈ a := by
        intro T
        refine Finset.induction_on T ?_ ?_
        · intro _
          obtain ⟨a, ha⟩ := hne
          exact ⟨a, ha, fun x hx => by simp at hx⟩
        · intro x T _ ih hTs
          obtain ⟨a, ha, haT⟩ := ih (fun y hy => hTs y (Finset.mem_insert_of_mem hy))
          obtain ⟨b, hb, hxb⟩ := (hmem x).mp (hTs x (Finset.mem_insert_self x T))
          rcases hchain a ha b hb with hab | hba
          · exact ⟨b, hb, fun y hy => by
              rcases Finset.mem_insert.mp hy with rfl | hy
              · exact hxb
              · exact hab (haT y hy)⟩
          · exact ⟨a, ha, fun y hy => by
              rcases Finset.mem_insert.mp hy with rfl | hy
              · exact hba hxb
              · exact haT y hy⟩
      exact hmain S hSall
    obtain ⟨a₀, ha₀c, ha₀⟩ := hex
    have htop_le : (⊤ : Subgroup G) ≤ a₀ := by
      rw [← hS.isGeneratingSet]
      exact (Subgroup.closure_le a₀).mpr ha₀
    exact htop (eq_top_iff.mpr htop_le ▸ ha₀c)
  exact ⟨U, hUne, hle⟩

/-! ## Maximal subgroups contain the kernel of the evaluation map -/

/-- Every maximal subgroup `M` of `G` contains `(evalHom p G).ker`, i.e. `M` is the kernel of some
homomorphism `G →* 𝔽_p`.  This is the step that uses both hypotheses: `M` has finite index
(`hmax`), so the finite quotient `G ⧸ core M` is a `p`-group (`hquot`), in which the image of `M`
is a maximal subgroup, hence normal of index `p`. -/
theorem ker_eval_le_of_isCoatom {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Group.FG G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup p (G ⧸ N))
    (hmax : ∀ M : Subgroup G, IsCoatom M → M.FiniteIndex)
    {M : Subgroup G} (hM : IsCoatom M) : (evalHom p G).ker ≤ M := by
  classical
  haveI hMfi : M.FiniteIndex := hmax M hM
  set N : Subgroup G := M.normalCore with hNdef
  have hNle : N ≤ M := M.normalCore_le
  haveI hNnorm : N.Normal := M.normalCore_normal
  haveI hNfi : N.FiniteIndex := M.finiteIndex_normalCore
  haveI hNfin : Finite (G ⧸ N) := inferInstance
  have hpQ : IsPGroup p (G ⧸ N) := hquot N hNfin
  set P : Subgroup (G ⧸ N) := M.map (QuotientGroup.mk' N) with hPdef
  have hkerle : (QuotientGroup.mk' N).ker ≤ M := by
    rw [QuotientGroup.ker_mk']
    exact hNle
  have hP : IsCoatom P :=
    Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le (QuotientGroup.mk'_surjective N) hM hkerle
  haveI hPn : P.Normal := by
    haveI : Group.IsNilpotent (G ⧸ N) := hpQ.isNilpotent
    exact Subgroup.NormalizerCondition.normal_of_coatom P
      (Group.normalizerCondition_of_isNilpotent) hP
  have hcard : Nat.card ((G ⧸ N) ⧸ P) = p :=
    Commons.GroupTheory.PGroup.natCard_quotient_coatom_eq_prime hpQ hP
  haveI hne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hcycR : IsCyclic ((G ⧸ N) ⧸ P) := isCyclic_of_prime_card hcard
  haveI hcycZ : IsCyclic (Multiplicative (ZMod p)) :=
    isCyclic_of_prime_card (by rw [natCard_multiplicative_zmod])
  have hiso : ((G ⧸ N) ⧸ P) ≃* Multiplicative (ZMod p) :=
    mulEquivOfCyclicCardEq (G := (G ⧸ N) ⧸ P) (G' := Multiplicative (ZMod p))
      (by rw [natCard_multiplicative_zmod]; exact hcard)
  intro x hx
  have hx1 : ∀ φ : HomFp p G, φ x = 1 := (mem_evalHom_ker x).mp hx
  set χ : HomFp p G :=
    hiso.toMonoidHom.comp ((QuotientGroup.mk' P).comp (QuotientGroup.mk' N)) with hχ
  have h1 : hiso ((QuotientGroup.mk' P) ((QuotientGroup.mk' N) x)) = 1 := hx1 χ
  have h2 : (QuotientGroup.mk' P) ((QuotientGroup.mk' N) x) = 1 :=
    hiso.injective (by rw [h1, map_one])
  have h3 : (QuotientGroup.mk' N) x ∈ P :=
    (QuotientGroup.eq_one_iff ((QuotientGroup.mk' N) x)).mp h2
  have h4 : P.comap (QuotientGroup.mk' N) = M := by
    rw [hPdef]
    exact Subgroup.comap_map_eq_self hkerle
  rw [← h4]
  exact h3

/-- The kernel of the evaluation map contains the Frattini subgroup of `G`. -/
theorem ker_eval_le_frattini {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Group.FG G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup p (G ⧸ N))
    (hmax : ∀ M : Subgroup G, IsCoatom M → M.FiniteIndex) :
    (evalHom p G).ker ≤ frattini G := by
  rw [frattini, Order.radical]
  refine le_iInf fun M => le_iInf fun hM => ker_eval_le_of_isCoatom hquot hmax hM

/-! ## The lifting step -/

/-- A generating set of `G ⧸ (evalHom p G).ker` lifts to a generating set of `G` of no larger
cardinality, because the kernel of the evaluation map contains the Frattini subgroup and the
Frattini subgroup consists of non-generators. -/
theorem dGens_le_dGens_quot_ker_eval {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Group.FG G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup p (G ⧸ N))
    (hmax : ∀ M : Subgroup G, IsCoatom M → M.FiniteIndex) :
    dGens G ≤ dGens (G ⧸ (evalHom p G).ker) := by
  classical
  haveI hKfin : (evalHom p G).ker.FiniteIndex := finiteIndex_ker_eval
  haveI hFGQ : Group.FG (G ⧸ (evalHom p G).ker) :=
    Group.fg_of_surjective (f := QuotientGroup.mk' (evalHom p G).ker)
      (QuotientGroup.mk'_surjective _)
  haveI hcoat : IsCoatomic (Subgroup G) := isCoatomic_subgroup_of_fg
  obtain ⟨S, hSmin, hScard⟩ :=
    exists_minimalGeneratingSet (G := G ⧸ (evalHom p G).ker) hFGQ
  choose g hg using fun s : (G ⧸ (evalHom p G).ker) =>
    QuotientGroup.mk'_surjective (evalHom p G).ker s
  set T : Finset G := S.image g with hTdef
  have himage : (QuotientGroup.mk' (evalHom p G).ker) '' (T : Set G)
      = (S : Set (G ⧸ (evalHom p G).ker)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (by simpa [hTdef] using hx)
      exact by rw [hg s]; exact hs
    · intro hy
      exact ⟨g y, by simpa [hTdef] using Finset.mem_image_of_mem g hy, hg y⟩
  have hmap : Subgroup.map (QuotientGroup.mk' (evalHom p G).ker)
      (Subgroup.closure (T : Set G)) = ⊤ := by
    rw [MonoidHom.map_closure, himage, hSmin.isGeneratingSet]
  have hsup : Subgroup.closure (T : Set G) ⊔ (evalHom p G).ker = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (QuotientGroup.mk' (evalHom p G).ker) x ∈
        Subgroup.map (QuotientGroup.mk' (evalHom p G).ker) (Subgroup.closure (T : Set G)) := by
      rw [hmap]; trivial
    rw [Subgroup.mem_map] at hx
    obtain ⟨h, hh, hhx⟩ := hx
    have hmem : h⁻¹ * x ∈ (evalHom p G).ker := by
      rw [← QuotientGroup.ker_mk' (evalHom p G).ker, MonoidHom.mem_ker, map_mul, map_inv, hhx,
        inv_mul_cancel]
    rw [Subgroup.mem_sup_of_normal_right]
    exact ⟨h, hh, h⁻¹ * x, hmem, by group⟩
  have hsupΦ : Subgroup.closure (T : Set G) ⊔ frattini G = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le_sup le_rfl (ker_eval_le_frattini hquot hmax)
  have htop : Subgroup.closure (T : Set G) = ⊤ := frattini_nongenerating hsupΦ
  calc dGens G ≤ T.card := dGens_le_card htop
    _ ≤ S.card := Finset.card_image_le
    _ = dGens (G ⧸ (evalHom p G).ker) := hScard

theorem dGens_eq_pHomDim_of_maximal_finiteIndex {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Group.FG G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup p (G ⧸ N))
    (hmax : ∀ M : Subgroup G, IsCoatom M → M.FiniteIndex) :
    pHomDim p G = dGens G := by
  haveI hKfin : (evalHom p G).ker.FiniteIndex := finiteIndex_ker_eval
  haveI : Finite (G ⧸ (evalHom p G).ker) := inferInstance
  have hpQ : IsPGroup p (G ⧸ (evalHom p G).ker) := hquot (evalHom p G).ker inferInstance
  have h1 : pHomDim p G = pHomDim p (G ⧸ (evalHom p G).ker) := pHomDim_quot_ker_eval.symm
  have h2 : pHomDim p (G ⧸ (evalHom p G).ker) = dGens (G ⧸ (evalHom p G).ker) :=
    dGens_eq_pHomDim_of_isPGroup hpQ
  have h3 : dGens G ≤ pHomDim p G :=
    (dGens_le_dGens_quot_ker_eval (p := p) hquot hmax).trans (le_of_eq (h2.symm.trans h1.symm))
  exact le_antisymm (pHomDim_le_dGens (Fact.out : p.Prime).one_lt) h3

end Work.ProPDeficiency

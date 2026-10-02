import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.nibbleWSetup
import Submission.Work.Deep.Kahn.nibbleExistsGood
import Submission.Work.Deep.Kahn.lllPolyBound
import Submission.Work.Deep.Prob.LLL.lll_exists

/-!
# The Lovász-local-lemma step of the *wasteful* one-round nibble

`Work.Deep.Kahn.nibbleWExistsGood` is the analogue of `Work.Deep.Kahn.nibbleExistsGood` for
the *wasteful* (Reed--Sudakov / residual) update used by
`Work.Deep.Kahn.RegularisedNibbleStatement`:

* the bad list event at an edge `e` is `Round.badListSet`: the number of colours of `L e` that
  `e` **loses** in the round (the colours of activated edges meeting `e`) exceeds
  `Λ (1 - s) + η Λ`, where `s = Round.retention Λ C D K` (equivalently, the residual list
  `Round.residual ω e = L e \ Round.lost ω e` has at most `newLambda - η Λ` colours);
* the bad event at a pair `(x,γ)` is `Round.badDegSet`: the residual colour degree
  `Round.newColDeg ω x γ = #{e ∋ x | ¬ kept ω e, γ ∈ Round.residual ω e}` exceeds
  `newDeg Λ C D K + η D`.

The dependence structure is inherited from `NibbleLLL`:

* `Round.lost ω e` (and hence `Round.residual ω e`) depends only on the coordinates in
  `supp1 e`: an activated edge `g` can remove the colour `γ` from `L e` only when `γ ∈ L g`,
  i.e. only when `L g ∩ L e ≠ ∅`, and then `Round.colour ω g = γ` is decided by the
  coordinate of `g`; so `g ∈ supp1 e`;
* hence `Round.newColDeg ω x γ` depends only on `suppPair x γ = ⋃_{f ∈ colThru x γ} supp2 f`.

With the support-size and dependence-degree bounds of `NibbleLLL` and the numerical bound
`Work.Deep.Kahn.lllPolyBound`, the symmetric Lovász local lemma
`Work.Deep.Prob.LLL.lll_exists` produces a single outcome `ω` avoiding every bad event.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

variable {n c : ℕ}
variable {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
variable {L : 𝓗 → Finset (Fin c)}

namespace NibbleW

/-! ## The wasteful bad events depend only on `supp1` / `suppPair` -/

section Main

variable {K : ℕ} [NeZero K]

/-- An edge meeting `e` and carrying a colour of `L e` belongs to the one-step support of
`e`. -/
lemma mem_supp1_of_inter_nonempty {e g : 𝓗}
    (hgint : ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)
    {γ : Fin c} (hγg : γ ∈ L g) (hγe : γ ∈ L e) :
    g ∈ NibbleLLL.supp1 (L := L) e := by
  rw [NibbleLLL.mem_supp1]
  by_cases hge : g = e
  · exact Or.inl hge
  · exact Or.inr ⟨hge, hgint, ⟨γ, Finset.mem_inter.mpr ⟨hγg, hγe⟩⟩⟩

/-- Transfer of activation and colour across agreement on `supp1 e`. -/
lemma active_colour_transfer {ω ω' : Round.Space K 𝓗 L} {e g : 𝓗} {γ : Fin c}
    (h : ∀ f ∈ NibbleLLL.supp1 (L := L) e, ω f = ω' f)
    (hγe : γ ∈ L e) (hga : Round.active ω g) (hgc : Round.colour ω g = γ)
    (hgi : ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty) :
    Round.active ω' g ∧ Round.colour ω' g = γ := by
  have hγg : γ ∈ L g := by rw [← hgc]; exact Round.colour_mem ω g
  have hgs : g ∈ NibbleLLL.supp1 (L := L) e :=
    mem_supp1_of_inter_nonempty hgi hγg hγe
  have hgg : ω g = ω' g := h g hgs
  exact ⟨(NibbleLLL.active_congr hgg).mp hga, (NibbleLLL.colour_congr hgg).symm.trans hgc⟩

/-- **The colours lost by `e` depend only on the coordinates in `supp1 e`.** -/
lemma lost_eq_of_agree {ω ω' : Round.Space K 𝓗 L} {e : 𝓗}
    (h : ∀ g ∈ NibbleLLL.supp1 (L := L) e, ω g = ω' g) :
    Round.lost ω e = Round.lost ω' e := by
  classical
  ext γ
  rw [Round.mem_lost, Round.mem_lost]
  constructor
  · rintro ⟨hγL, g, hga, hgc, hgi⟩
    obtain ⟨hga', hgc'⟩ := active_colour_transfer h hγL hga hgc hgi
    exact ⟨hγL, g, hga', hgc', hgi⟩
  · rintro ⟨hγL, g, hga, hgc, hgi⟩
    obtain ⟨hga', hgc'⟩ :=
      active_colour_transfer (ω := ω') (ω' := ω) (fun f hf => (h f hf).symm) hγL hga hgc hgi
    exact ⟨hγL, g, hga', hgc', hgi⟩

/-- **The residual list of `e` depends only on the coordinates in `supp2 e`.** -/
lemma residual_eq_of_agree {ω ω' : Round.Space K 𝓗 L} {e : 𝓗}
    (h : ∀ g ∈ NibbleLLL.supp2 (L := L) e, ω g = ω' g) :
    Round.residual ω e = Round.residual ω' e := by
  classical
  have h1 : ∀ f ∈ NibbleLLL.supp1 (L := L) e, ω f = ω' f :=
    fun f hf => h f (NibbleLLL.supp1_subset_supp2_self e hf)
  ext γ
  rw [Round.mem_residual, Round.mem_residual]
  constructor
  · rintro ⟨hγL, hno⟩
    refine ⟨hγL, fun g hga hgc hgi => ?_⟩
    have hγg : γ ∈ L g := by rw [← hgc]; exact Round.colour_mem ω' g
    have hgs : g ∈ NibbleLLL.supp1 (L := L) e := mem_supp1_of_inter_nonempty hgi hγg hγL
    have hgg : ω g = ω' g := h1 g hgs
    exact hno g ((NibbleLLL.active_congr hgg).mpr hga)
      ((NibbleLLL.colour_congr hgg).trans hgc) hgi
  · rintro ⟨hγL, hno⟩
    refine ⟨hγL, fun g hga hgc hgi => ?_⟩
    have hγg : γ ∈ L g := by rw [← hgc]; exact Round.colour_mem ω g
    have hgs : g ∈ NibbleLLL.supp1 (L := L) e := mem_supp1_of_inter_nonempty hgi hγg hγL
    have hgg : ω g = ω' g := h1 g hgs
    exact hno g ((NibbleLLL.active_congr hgg).mp hga)
      ((NibbleLLL.colour_congr hgg).symm.trans hgc) hgi

/-- **The bad list event depends only on the coordinates in `supp2 e`.** -/
lemma badListSet_congr (C D Λ : ℕ) (η : ℝ) {ω ω' : Round.Space K 𝓗 L} {e : 𝓗}
    (h : ∀ g ∈ NibbleLLL.supp2 (L := L) e, ω g = ω' g) :
    (ω ∈ Round.badListSet (K := K) (L := L) C D Λ η e ↔
      ω' ∈ Round.badListSet (K := K) (L := L) C D Λ η e) := by
  have h1 : ∀ g ∈ NibbleLLL.supp1 (L := L) e, ω g = ω' g :=
    fun g hg => h g (NibbleLLL.supp1_subset_supp2_self e hg)
  have hcard : (Round.lost ω e).card = (Round.lost ω' e).card :=
    congrArg Finset.card (lost_eq_of_agree h1)
  simp only [Round.badListSet, Set.mem_ofPred_eq, hcard]

/-- **The residual colour degree depends only on the coordinates in `suppPair x γ`.** -/
lemma newColDeg_eq_of_agree {ω ω' : Round.Space K 𝓗 L} {x : Fin n} {γ : Fin c}
    (h : ∀ g ∈ NibbleLLL.suppPair (L := L) x γ, ω g = ω' g) :
    Round.newColDeg ω x γ = Round.newColDeg ω' x γ := by
  classical
  have hfilter : (Finset.univ.filter (fun e : 𝓗 => ¬ Round.kept ω e ∧
        x ∈ (e : Set (Fin n)) ∧ γ ∈ Round.residual ω e))
      = (Finset.univ.filter (fun e : 𝓗 => ¬ Round.kept ω' e ∧
        x ∈ (e : Set (Fin n)) ∧ γ ∈ Round.residual ω' e)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hk, hxe, hres⟩
      have hγe : γ ∈ L e := (Round.mem_residual.mp hres).1
      have hec : e ∈ NibbleLLL.colThru (L := L) x γ :=
        NibbleLLL.mem_colThru.mpr ⟨hxe, hγe⟩
      have hsub : NibbleLLL.supp2 (L := L) e ⊆ NibbleLLL.suppPair (L := L) x γ :=
        NibbleLLL.supp2_subset_suppPair hec
      have hke : (Round.kept ω e ↔ Round.kept ω' e) :=
        NibbleLLL.kept_congr
          (fun g hg => h g (hsub (NibbleLLL.supp1_subset_supp2_self e hg)))
      have hre : γ ∈ Round.residual ω' e := by
        rw [← residual_eq_of_agree (fun g hg => h g (hsub hg))]
        exact hres
      exact ⟨fun hk' => hk (hke.mpr hk'), hxe, hre⟩
    · rintro ⟨hk, hxe, hres⟩
      have hγe : γ ∈ L e := (Round.mem_residual.mp hres).1
      have hec : e ∈ NibbleLLL.colThru (L := L) x γ :=
        NibbleLLL.mem_colThru.mpr ⟨hxe, hγe⟩
      have hsub : NibbleLLL.supp2 (L := L) e ⊆ NibbleLLL.suppPair (L := L) x γ :=
        NibbleLLL.supp2_subset_suppPair hec
      have hke : (Round.kept ω e ↔ Round.kept ω' e) :=
        NibbleLLL.kept_congr
          (fun g hg => h g (hsub (NibbleLLL.supp1_subset_supp2_self e hg)))
      have hre : γ ∈ Round.residual ω e := by
        rw [residual_eq_of_agree (fun g hg => h g (hsub hg))]
        exact hres
      exact ⟨fun hk' => hk (hke.mp hk'), hxe, hre⟩
  show (Finset.univ.filter (fun e : 𝓗 => ¬ Round.kept ω e ∧
      x ∈ (e : Set (Fin n)) ∧ γ ∈ Round.residual ω e)).card
    = (Finset.univ.filter (fun e : 𝓗 => ¬ Round.kept ω' e ∧
      x ∈ (e : Set (Fin n)) ∧ γ ∈ Round.residual ω' e)).card
  rw [hfilter]

/-- **The residual colour-degree bad event depends only on the coordinates in `suppPair x γ`.**
-/
lemma badDegSet_congr (C D Λ : ℕ) (η : ℝ) {ω ω' : Round.Space K 𝓗 L} {x : Fin n}
    {γ : Fin c} (h : ∀ g ∈ NibbleLLL.suppPair (L := L) x γ, ω g = ω' g) :
    (ω ∈ Round.badDegSet (K := K) (L := L) C D Λ η x γ ↔
      ω' ∈ Round.badDegSet (K := K) (L := L) C D Λ η x γ) := by
  have hcard : Round.newColDeg ω x γ = Round.newColDeg ω' x γ := newColDeg_eq_of_agree h
  simp only [Round.badDegSet, Set.mem_ofPred_eq, hcard]

/-- The bad event of the wasteful round attached to an index: the list event at an edge, the
residual colour-degree event at an occurring pair. -/
def badEventW (C D Λ : ℕ) (η : ℝ) {K : ℕ} [NeZero K] :
    NibbleLLL.BadIdx (L := L) → Set (Round.Space K 𝓗 L) :=
  Sum.elim (fun e : 𝓗 => Round.badListSet (K := K) (L := L) C D Λ η e)
    (fun p => Round.badDegSet (K := K) (L := L) C D Λ η p.1.1 p.1.2)

/-- The wasteful bad event at an index depends only on the coordinates in its support. -/
lemma badEventW_congr (C D Λ : ℕ) (η : ℝ) (i : NibbleLLL.BadIdx (L := L))
    {ω ω' : Round.Space K 𝓗 L}
    (h : ∀ g ∈ NibbleLLL.suppOf (L := L) i, ω g = ω' g) :
    (ω ∈ badEventW C D Λ η i ↔ ω' ∈ badEventW C D Λ η i) := by
  rcases i with e | p
  · exact badListSet_congr C D Λ η h
  · exact badDegSet_congr C D Λ η h

end Main

/-! ## Independence of the wasteful bad events with disjoint supports -/

section Indep

variable {K : ℕ} [NeZero K] [Nonempty (Round.Space K 𝓗 L)]

/-- **Two wasteful bad events with disjoint supports are independent** (in the product measure
of the round): the independence hypothesis of the symmetric Lovász local lemma. -/
lemma indepOfCompls_badEventW (C D Λ : ℕ) (η : ℝ)
    (i : NibbleLLL.BadIdx (L := L)) (T : Finset (NibbleLLL.BadIdx (L := L)))
    (hT : ∀ j ∈ T, j ∉ NibbleLLL.depSet (L := L) i ∧ j ≠ i) :
    (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).indepOfCompls
      (badEventW C D Λ η i) (badEventW C D Λ η) T := by
  classical
  have hneFib : ∀ e : 𝓗, Nonempty (Round.Coord K 𝓗 L e) :=
    fun e => ⟨(Classical.arbitrary (Round.Space K 𝓗 L)) e⟩
  have hdisj : Disjoint (NibbleLLL.suppOf (L := L) i)
      (T.biUnion (fun j => NibbleLLL.suppOf (L := L) j)) := by
    rw [Finset.disjoint_left]
    intro g hgS hgR
    rw [Finset.mem_biUnion] at hgR
    obtain ⟨j, hj, hgj⟩ := hgR
    have hcon : (NibbleLLL.suppOf (L := L) j ∩ NibbleLLL.suppOf (L := L) i).Nonempty :=
      ⟨g, Finset.mem_inter.mpr ⟨hgj, hgS⟩⟩
    have hmem : j ∈ NibbleLLL.depSet (L := L) i := by
      rw [NibbleLLL.depSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hT j hj).2, hcon⟩
    exact (hT j hj).1 hmem
  have hdetX : ∀ ω ω' : Round.Space K 𝓗 L,
      (∀ g ∈ NibbleLLL.suppOf (L := L) i, ω g = ω' g) →
      (ω ∈ badEventW C D Λ η i ↔ ω' ∈ badEventW C D Λ η i) :=
    fun _ _ h => badEventW_congr C D Λ η i h
  have hdetY : ∀ ω ω' : Round.Space K 𝓗 L,
      (∀ g ∈ T.biUnion (fun j => NibbleLLL.suppOf (L := L) j), ω g = ω' g) →
      (ω ∈ ⋂ j ∈ T, (badEventW C D Λ η j)ᶜ ↔
        ω' ∈ ⋂ j ∈ T, (badEventW C D Λ η j)ᶜ) := by
    intro ω ω' h
    have hmem : ∀ j ∈ T, (ω ∈ (badEventW C D Λ η j)ᶜ ↔
        ω' ∈ (badEventW C D Λ η j)ᶜ) := by
      intro j hj
      have hsub : NibbleLLL.suppOf (L := L) j ⊆
          T.biUnion (fun j => NibbleLLL.suppOf (L := L) j) :=
        fun g hg => Finset.mem_biUnion.mpr ⟨j, hj, hg⟩
      exact not_congr (badEventW_congr C D Λ η j (fun g hg => h g (hsub hg)))
    rw [Set.mem_iInter₂, Set.mem_iInter₂]
    exact forall₂_congr hmem
  have hconc : Work.Deep.Conc.prob
      ((badEventW C D Λ η i) ∩ ⋂ j ∈ T, (badEventW C D Λ η j)ᶜ)
      = Work.Deep.Conc.prob (badEventW C D Λ η i) *
        Work.Deep.Conc.prob (⋂ j ∈ T, (badEventW C D Λ η j)ᶜ) :=
    Work.Deep.Conc.prob_inter_eq_mul_of_determined (π := fun e : 𝓗 => Round.Coord K 𝓗 L e)
      hneFib hdisj hdetX hdetY
  show (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).prob
      ((badEventW C D Λ η i) ∩ ⋂ j ∈ T, (badEventW C D Λ η j)ᶜ)
      = (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).prob
          (badEventW C D Λ η i) *
        (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).prob
          (⋂ j ∈ T, (badEventW C D Λ η j)ᶜ)
  rw [← NibbleLLL.conc_prob_eq_uniform_prob, ← NibbleLLL.conc_prob_eq_uniform_prob,
    ← NibbleLLL.conc_prob_eq_uniform_prob]
  exact hconc

end Indep

end NibbleW

theorem nibbleWExistsGood {C : ℕ} (hC : 2 ≤ C) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Dmin : ℝ, 0 < Dmin ∧
    Dmin ≤ ((C : ℝ) + η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) + 10 ^ (1000 : ℕ) ∧
    ∀ (n c : ℕ)
      (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗]
      (L : 𝓗 → Finset (Fin c)) (D Λ K : ℕ) [NeZero K],
      1 ≤ D → 1 ≤ Λ → 2 ≤ K → η * (K : ℝ) ≤ 1 →
      (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) →
      𝓗.IsLinear →
      (∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C) →
      (∀ e : 𝓗, (L e).card = Λ) →
      (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D) →
      (1 + ε) * (D : ℝ) ≤ (Λ : ℝ) → (Λ : ℝ) ≤ 10 * (C : ℝ) * (D : ℝ) →
      Dmin ≤ (D : ℝ) →
      Real.log (D : ℝ) ≤ (K : ℝ) → (K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2 →
      ((C : ℝ) + (K : ℝ) + η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) →
      (∀ e : 𝓗,
        Work.Deep.Conc.prob (Work.Deep.Kahn.Round.badListSet (K := K) (L := L) C D Λ η e)
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4))) →
      (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Work.Deep.Conc.prob (Work.Deep.Kahn.Round.badDegSet (K := K) (L := L) C D Λ η x γ)
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4))) →
      ∃ ω : Work.Deep.Kahn.Round.Space K 𝓗 L,
        (∀ e : 𝓗, ¬ Work.Deep.Kahn.Round.kept ω e →
          Work.Deep.Kahn.newLambda Λ C D K - η * (Λ : ℝ) ≤
            ((Work.Deep.Kahn.Round.residual ω e).card : ℝ)) ∧
        (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
          ((Work.Deep.Kahn.Round.newColDeg ω x γ : ℕ) : ℝ) ≤
            Work.Deep.Kahn.newDeg Λ C D K + η * (D : ℝ)) := by
  refine ⟨(2 : ℝ) ^ 80, by positivity, ?_, ?_⟩
  · -- the polynomial lower bound on the threshold
    -- (no `linarith` here: its preprocessing expands the huge power `(⋯)^1000`)
    have hbase : (2 : ℝ) ^ (80 : ℕ) ≤ (10 : ℝ) ^ (1000 : ℕ) := by
      have h1 : (2 : ℝ) ^ (80 : ℕ) ≤ (2 : ℝ) ^ (1000 : ℕ) :=
        pow_le_pow_right₀ (by norm_num) (by norm_num)
      have h2 : (2 : ℝ) ^ (1000 : ℕ) ≤ (10 : ℝ) ^ (1000 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) 1000
      exact le_trans h1 h2
    have h10 : (10 : ℝ) ^ (1000 : ℕ) ≤
        ((C : ℝ) + η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) + 10 ^ (1000 : ℕ) := by
      have hX : (0 : ℝ) ≤ ((C : ℝ) + η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) := by positivity
      exact le_add_of_nonneg_left hX
    exact le_trans hbase h10
  · intro n c 𝓗 instF L D Λ K instK hD hΛ hK hηK h16 hlin hsize hlist hdeg hεD hΛ10
      hDmin hlogD hKD hCKD hUsed hKept
    classical
    -- the round space is nonempty
    haveI hSpaceNe : Nonempty (Round.Space K 𝓗 L) :=
      ⟨fun e => (⟨0, by omega⟩, ⟨0, by rw [hlist e]; omega⟩)⟩
    -- the numerical hypotheses in ℕ
    have hΛ10' : Λ ≤ 10 * C * D := by exact_mod_cast hΛ10
    have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have hCD : C ≤ D := by
      have h1 : (C : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := by
        have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
        have hη0 : (0 : ℝ) < η⁻¹ := inv_pos.mpr hη
        linarith [hCKD]
      have h2 : (D : ℝ) ^ ((1 : ℝ) / 9) ≤ (D : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le (x := (D : ℝ)) hD1R
          (by norm_num : ((1 : ℝ) / 9) ≤ 1)
      exact_mod_cast (le_trans h1 h2)
    -- the three hypotheses of the local lemma
    have hp : ∀ i : NibbleLLL.BadIdx (L := L),
        (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).prob
          (NibbleW.badEventW C D Λ η i) ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) := by
      intro i
      rcases i with e | p
      · rw [← NibbleLLL.conc_prob_eq_uniform_prob]
        exact hUsed e
      · rw [← NibbleLLL.conc_prob_eq_uniform_prob]
        exact hKept p.1.1 p.1.2 p.2
    have hd : ∀ i : NibbleLLL.BadIdx (L := L),
        (NibbleLLL.depSet (L := L) i).card ≤ NibbleLLL.DepDeg C D := by
      intro i
      refine le_trans (NibbleLLL.card_depSet_le hD hsize hlist hdeg i) ?_
      exact NibbleLLL.depBound_le_DepDeg hC hD hΛ10'
    have hindep : ∀ i (T : Finset (NibbleLLL.BadIdx (L := L))),
        (∀ j ∈ T, j ∉ NibbleLLL.depSet (L := L) i ∧ j ≠ i) →
        (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).indepOfCompls
          (NibbleW.badEventW C D Λ η i) (NibbleW.badEventW C D Λ η) T :=
      fun i T hT => NibbleW.indepOfCompls_badEventW C D Λ η i T hT
    have hpd : Real.exp 1 * Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) *
        (((NibbleLLL.DepDeg C D : ℕ) : ℝ) + 1) ≤ 1 := by
      have h := lllPolyBound (C := C) (D := D) (by omega) hCD hDmin
      simpa [NibbleLLL.DepDeg, Nat.cast_add, Nat.cast_one] using h
    -- the local lemma
    obtain ⟨ω, hω⟩ := Work.Deep.Prob.LLL.lll_exists
      (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L))
      (NibbleW.badEventW C D Λ η) (NibbleLLL.depSet (L := L)) hp hd hindep hpd
    refine ⟨ω, ?_, ?_⟩
    · -- the residual list keeps at least `newLambda - η Λ` colours
      intro e _
      have hbad : ω ∉ Round.badListSet (K := K) (L := L) C D Λ η e := by
        have h1 := hω (Sum.inl e)
        simpa [NibbleW.badEventW] using h1
      rw [Round.badListSet, Set.mem_ofPred_eq] at hbad
      push_neg at hbad
      have hsub : Round.lost ω e ⊆ L e := fun γ hγ => (Round.mem_lost.mp hγ).1
      have hcle : (Round.lost ω e).card ≤ Λ := by
        calc (Round.lost ω e).card ≤ (L e).card := Finset.card_le_card hsub
          _ = Λ := hlist e
      have hsdiff : (Round.residual ω e).card = Λ - (Round.lost ω e).card := by
        show (L e \ Round.lost ω e).card = Λ - (Round.lost ω e).card
        rw [Finset.card_sdiff, hlist e, Finset.inter_eq_left.mpr hsub]
      rw [hsdiff, Nat.cast_sub hcle, newLambda]
      have hkey : (Λ : ℝ) * retention Λ C D K - η * (Λ : ℝ)
          = (Λ : ℝ) - ((Λ : ℝ) * (1 - retention Λ C D K) + η * (Λ : ℝ)) := by ring
      rw [hkey]
      linarith
    · -- the residual colour degree is at most `newDeg + η D`
      intro x γ hocc
      have hbad : ω ∉ Round.badDegSet (K := K) (L := L) C D Λ η x γ := by
        have h1 := hω (Sum.inr (⟨(x, γ), hocc⟩ : NibbleLLL.Occ (L := L)))
        simpa [NibbleW.badEventW] using h1
      rw [Round.badDegSet, Set.mem_ofPred_eq] at hbad
      push_neg at hbad
      exact hbad

end

end Work.Deep.Kahn

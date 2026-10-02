import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.roundKeptUnactDefs
import Submission.Work.Deep.Kahn.boxProb
import Submission.Work.Deep.Kahn.keptEvidenceLaw

/-!
# `Work.Deep.Kahn.keptUnactMean`

The **mean of the unactivated-survivor count** `keptUnactCount ω x γ` (the paper's
`keptUnactColsRV`) on the uniform product space `Round.Space K 𝓗 L`:

  `E[keptUnactCount · x γ] = D * (1 - 1/K) * (1 - 1/(KΛ)) ^ ((C-1)(D-1))`.

The exponent `(C-1)(D-1)` is the **exact** number of candidate blockers of a `γ`-edge `e ∋ x`:
linearity splits them, according to the vertex of `e \ {x}` they meet, into `C-1` groups of
`D-1` edges; each such blocker is activated with colour `γ` with probability `1/(KΛ)`, and the
coordinate of `e` itself is activated with probability `1/K`.  (The paper writes `D(C-1)`, the
value for *nearly disjoint graphs*, which is one `(C-1)` larger; `retentionU` uses that larger
exponent, and `Work.Deep.Kahn.keptUnactThresh` bridges the difference.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

namespace Round

/-- The candidate blockers of `e` split, according to the vertex of `e \ {x}` they meet, into
the `D-1` other `γ`-edges through that vertex. -/
lemma blockSet_card {n c C D : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] {L : 𝓗 → Finset (Fin c)}
    (hlin : ErdosFaberLovaszConjecture.Hypergraph.IsLinear 𝓗)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    {x : Fin n} {γ : Fin c} {e : 𝓗} (he : e ∈ colThru (L := L) x γ) :
    (blockSet (L := L) x γ e).card = (C - 1) * (D - 1) := by
  classical
  have hxe : x ∈ (e : Set (Fin n)) := (mem_colThru.mp he).1
  have hγe : γ ∈ L e := (mem_colThru.mp he).2
  have hthrough : ∀ y : Fin n, y ∈ (e : Set (Fin n)) → (colThru (L := L) y γ).card = D :=
    fun y hy => colThru_card (L := L) hdeg ⟨e, hy, hγe⟩
  have hunion : blockSet (L := L) x γ e
      = ((verts (e : Set (Fin n))).erase x).biUnion
          (fun y => (colThru (L := L) y γ).erase e) := by
    ext f
    rw [mem_blockSet, Finset.mem_biUnion]
    constructor
    · rintro ⟨hxf, hγf, hinte⟩
      obtain ⟨y, hyf, hye⟩ := hinte
      exact ⟨y, Finset.mem_erase.mpr ⟨fun hyx => hxf (hyx ▸ hyf), (by simpa [verts] using hye)⟩,
        Finset.mem_erase.mpr ⟨fun hfe => hxf (hfe ▸ hxe),
          mem_colThru.mpr ⟨hyf, hγf⟩⟩⟩
    · rintro ⟨y, hy, hf⟩
      obtain ⟨hyx, hye⟩ := Finset.mem_erase.mp hy
      obtain ⟨hfe, hfc⟩ := Finset.mem_erase.mp hf
      obtain ⟨hyf, hγf⟩ := mem_colThru.mp hfc
      refine ⟨?_, hγf, ⟨y, hyf, (by simpa [verts] using hye)⟩⟩
      intro hxf
      have hsub : ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Subsingleton :=
        hlin f.2 e.2 (fun hc => hfe (Subtype.ext hc))
      exact hyx (hsub ⟨hyf, (by simpa [verts] using hye)⟩ ⟨hxf, hxe⟩)
  have hdisj : ((↑((verts (e : Set (Fin n))).erase x) : Set (Fin n))).PairwiseDisjoint
      (fun y => (colThru (L := L) y γ).erase e) := by
    intro y hy y' hy' hne
    show Disjoint ((colThru (L := L) y γ).erase e) ((colThru (L := L) y' γ).erase e)
    rw [Finset.disjoint_left]
    intro f hf hf'
    obtain ⟨hfe, hfc⟩ := Finset.mem_erase.mp hf
    obtain ⟨-, hfc'⟩ := Finset.mem_erase.mp hf'
    obtain ⟨hyf, -⟩ := mem_colThru.mp hfc
    obtain ⟨hy'f, -⟩ := mem_colThru.mp hfc'
    have hye : y ∈ (e : Set (Fin n)) :=
      (mem_verts (e : Set (Fin n)) y).mp
        (Finset.mem_erase.mp (by simpa only [Finset.mem_coe] using hy)).2
    have hy'e : y' ∈ (e : Set (Fin n)) :=
      (mem_verts (e : Set (Fin n)) y').mp
        (Finset.mem_erase.mp (by simpa only [Finset.mem_coe] using hy')).2
    have hsub : ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Subsingleton :=
      hlin f.2 e.2 (fun hc => hfe (Subtype.ext hc))
    exact hne (hsub ⟨hyf, hye⟩ ⟨hy'f, hy'e⟩)
  have hpiece : ∀ y ∈ (verts (e : Set (Fin n))).erase x,
      ((colThru (L := L) y γ).erase e).card = D - 1 := by
    intro y hy
    have hye : y ∈ (e : Set (Fin n)) :=
      (by simpa [verts] using (Finset.mem_erase.mp hy).2)
    rw [Finset.card_erase_of_mem (mem_colThru.mpr ⟨hye, hγe⟩), hthrough y hye]
  rw [hunion, Finset.card_biUnion hdisj, Finset.sum_congr rfl hpiece, Finset.sum_const,
    smul_eq_mul]
  have hcard : ((verts (e : Set (Fin n))).erase x).card = C - 1 := by
    rw [Finset.card_erase_of_mem ((by simpa [verts] using hxe))]
    have h2 : (verts (e : Set (Fin n))).card = C := hsize e
    omega
  rw [hcard]

/-- The probability that a fixed `γ`-edge `e` through `x` is counted is
`(1 - 1/K) (1 - 1/(KΛ))^{|blockSet x γ e|}`. -/
lemma prob_counted {n c Λ K : ℕ} [NeZero K]
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] {L : 𝓗 → Finset (Fin c)}
    (hlist : ∀ e : 𝓗, (L e).card = Λ) (hΛ1 : 1 ≤ Λ) {x : Fin n} {γ : Fin c} {e : 𝓗}
    (he : e ∈ colThru (L := L) x γ) :
    Work.Deep.Conc.prob {ω : Space K 𝓗 L | counted (K := K) ω x γ e}
      = (1 - 1 / (K : ℝ))
        * (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ ((blockSet (L := L) x γ e).card) := by
  classical
  have hxe : x ∈ (e : Set (Fin n)) := (mem_colThru.mp he).1
  have hemem : e ∉ blockSet (L := L) x γ e := not_mem_blockSet_self (L := L) hxe
  have hne : ∀ f : 𝓗, Nonempty (Coord K 𝓗 L f) :=
    fun f => ⟨(0, ⟨0, by rw [hlist f]; omega⟩)⟩
  set A : ∀ f : 𝓗, Finset (Coord K 𝓗 L f) := fun f =>
    if f = e then Finset.univ.filter (fun a : Coord K 𝓗 L f => a.1 ≠ 0)
    else goodIndex (L := L) (K := K) f γ with hAdef
  have hbox_eq : {ω : Space K 𝓗 L | counted (K := K) ω x γ e}
      = {ω : Space K 𝓗 L | ∀ i ∈ insert e (blockSet (L := L) x γ e), ω i ∈ A i} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    have hAe : ω e ∈ A e ↔ ¬ active ω e := by
      simp only [A, if_pos rfl, Finset.mem_filter, Finset.mem_univ, true_and, active]
    have hAf : ∀ f ∈ blockSet (L := L) x γ e,
        (ω f ∈ A f ↔ ¬ (active ω f ∧ colour ω f = γ)) := by
      intro f hf
      have hfe : f ≠ e := fun h => hemem (h ▸ hf)
      rw [show A f = goodIndex (L := L) (K := K) f γ from by simp only [A, if_neg hfe],
        mem_goodIndex]
      simp only [active, round_colour_eq_idxColour]
    constructor
    · intro h i hi
      rcases Finset.mem_insert.mp hi with rfl | hiB
      · exact hAe.mpr h.1
      · exact (hAf i hiB).mpr (fun hcon =>
          h.2 ((isBlocked_iff_blockSet (K := K) ω x γ e).mpr ⟨i, hiB, hcon.1, hcon.2⟩))
    · intro h
      refine ⟨hAe.mp (h e (Finset.mem_insert_self e (blockSet (L := L) x γ e))), ?_⟩
      intro hb
      obtain ⟨f, hfB, ha, hc⟩ := (isBlocked_iff_blockSet (K := K) ω x γ e).mp hb
      exact (hAf f hfB).mp (h f (Finset.mem_insert_of_mem hfB)) ⟨ha, hc⟩
  rw [hbox_eq, box_prob (π := fun f : 𝓗 => Coord K 𝓗 L f) hne
    (insert e (blockSet (L := L) x γ e)) A]
  rw [Finset.prod_insert hemem]
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
    exact_mod_cast this
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ1
  have hfac : ∀ f ∈ blockSet (L := L) x γ e,
      ((A f).card : ℝ) / (Fintype.card (Coord K 𝓗 L f) : ℝ)
        = 1 - 1 / ((K : ℝ) * (Λ : ℝ)) := by
    intro f hf
    obtain ⟨hxf, hγf, -⟩ := mem_blockSet.mp hf
    have hfe : f ≠ e := fun h => hxf (h ▸ hxe)
    have hcf' : Fintype.card (Coord K 𝓗 L f) = K * Λ := by
      rw [show Fintype.card (Coord K 𝓗 L f) = Fintype.card (Fin K × Fin (L f).card) from rfl,
        Fintype.card_prod, Fintype.card_fin, hlist f, Fintype.card_fin]
    have h1 : 1 ≤ K * Λ := by rw [← hcf']; exact Fintype.card_pos_iff.mpr (hne f)
    have hAcard : (A f).card = Fintype.card (Fin K × Fin (L f).card) - 1 := by
      rw [show A f = goodIndex (L := L) (K := K) f γ from by simp only [A, if_neg hfe],
        card_goodIndex, if_pos hγf]
    have hKLne : ((K : ℝ) * (Λ : ℝ)) ≠ 0 := by positivity
    rw [hAcard, hcf', Nat.cast_sub h1]
    push_cast
    field_simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_const]
  have hfirst : ((A e).card : ℝ) / (Fintype.card (Coord K 𝓗 L e) : ℝ)
      = 1 - 1 / (K : ℝ) := by
    have hcf' : Fintype.card (Coord K 𝓗 L e) = K * Λ := by
      rw [show Fintype.card (Coord K 𝓗 L e) = Fintype.card (Fin K × Fin (L e).card) from rfl,
        Fintype.card_prod, Fintype.card_fin, hlist e, Fintype.card_fin]
    have hzero : (Finset.univ.filter (fun a : Coord K 𝓗 L e => a.1 = 0)).card = Λ := by
      have hset : (Finset.univ.filter (fun a : Coord K 𝓗 L e => a.1 = 0))
          = (Finset.univ : Finset (Fin (L e).card)).image (fun i => ((0 : Fin K), i)) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨fun ha => ⟨a.2, Prod.ext ha.symm rfl⟩, by rintro ⟨i, rfl⟩; rfl⟩
      rw [hset, Finset.card_image_of_injective _ (fun i j h => (Prod.mk.inj h).2),
        Finset.card_univ, Fintype.card_fin, hlist e]
    have hsplit : (Finset.univ.filter (fun a : Coord K 𝓗 L e => a.1 ≠ 0)).card
        + (Finset.univ.filter (fun a : Coord K 𝓗 L e => a.1 = 0)).card = K * Λ := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Coord K 𝓗 L e)))
        (p := fun a : Coord K 𝓗 L e => a.1 ≠ 0)
      have hnot : (Finset.univ.filter (fun a : Coord K 𝓗 L e => ¬ (a.1 ≠ 0)))
          = Finset.univ.filter (fun a : Coord K 𝓗 L e => a.1 = 0) := by
        refine Finset.filter_congr (fun a _ => ?_)
        simp
      rw [hnot] at h
      rwa [Finset.card_univ, hcf'] at h
    rw [hzero] at hsplit
    have hAe_eq : A e = Finset.univ.filter (fun a : Coord K 𝓗 L e => a.1 ≠ 0) := by
      simp only [A, if_pos rfl]
    rw [hAe_eq]
    have hkey : (K - 1) * Λ + Λ = K * Λ := by
      calc (K - 1) * Λ + Λ = (K - 1) * Λ + 1 * Λ := by rw [one_mul]
        _ = ((K - 1) + 1) * Λ := (Nat.add_mul _ _ _).symm
        _ = K * Λ := by
              rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne K))]
    have hcard : (Finset.univ.filter (fun a : Coord K 𝓗 L e => a.1 ≠ 0)).card
        = (K - 1) * Λ := by omega
    rw [hcard, hcf', Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)), Nat.cast_one]
    field_simp
  rw [hfirst]

theorem keptUnactMean {n c C D Λ K : ℕ} [NeZero K]
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] {L : 𝓗 → Finset (Fin c)}
    (hlin : ErdosFaberLovaszConjecture.Hypergraph.IsLinear 𝓗)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (hlist : ∀ e : 𝓗, (L e).card = Λ) {x : Fin n} {γ : Fin c}
    (hxγ : ∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) :
    Work.Deep.Conc.expect (fun ω : Space K 𝓗 L => (keptUnactCount ω x γ : ℝ))
      = (D : ℝ) * (1 - 1 / (K : ℝ))
        * (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ ((C - 1) * (D - 1)) := by
  classical
  have hΛ1 : 1 ≤ Λ := by
    obtain ⟨e, he, hγ⟩ := hxγ
    rw [← hlist e]
    exact Finset.card_pos.mpr ⟨γ, hγ⟩
  have hBcard : ∀ e ∈ colThru (L := L) x γ,
      (blockSet (L := L) x γ e).card = (C - 1) * (D - 1) :=
    fun e he => blockSet_card (L := L) hlin hsize hdeg he
  have hsingle := fun e (he : e ∈ colThru (L := L) x γ) =>
    prob_counted (L := L) (K := K) hlist hΛ1 he
  have hsum : ∀ ω : Space K 𝓗 L, (keptUnactCount ω x γ : ℝ)
      = ∑ e ∈ colThru (L := L) x γ, (if counted (K := K) ω x γ e then (1 : ℝ) else 0) := by
    intro ω
    rw [keptUnactCount_eq_card (K := K) ω x γ, keptUnactSet]
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h : counted (K := K) ω x γ e <;> simp [h]
  calc Work.Deep.Conc.expect (fun ω : Space K 𝓗 L => (keptUnactCount ω x γ : ℝ))
      = Work.Deep.Conc.expect (fun ω : Space K 𝓗 L =>
          ∑ e ∈ colThru (L := L) x γ,
            (if counted (K := K) ω x γ e then (1 : ℝ) else 0)) :=
        Work.Deep.Conc.expect_congr hsum
    _ = ∑ e ∈ colThru (L := L) x γ, Work.Deep.Conc.expect
          (fun ω : Space K 𝓗 L =>
            (if counted (K := K) ω x γ e then (1 : ℝ) else 0)) :=
        Work.Deep.Conc.expect_sum _ _
    _ = ∑ e ∈ colThru (L := L) x γ,
          Work.Deep.Conc.prob {ω : Space K 𝓗 L | counted (K := K) ω x γ e} := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Work.Deep.Conc.prob]
        exact Work.Deep.Conc.expect_congr (fun ω => by
          simp only [Set.indicator_apply, Set.mem_ofPred_eq])
    _ = ∑ e ∈ colThru (L := L) x γ, (1 - 1 / (K : ℝ))
          * (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ ((blockSet (L := L) x γ e).card) :=
        Finset.sum_congr rfl hsingle
    _ = (1 - 1 / (K : ℝ)) * (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ ((C - 1) * (D - 1))
          * (colThru (L := L) x γ).card := by
        rw [Finset.sum_congr rfl (fun e he => by rw [hBcard e he]), Finset.sum_const,
          nsmul_eq_mul]
        ring
    _ = (D : ℝ) * (1 - 1 / (K : ℝ))
          * (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ ((C - 1) * (D - 1)) := by
        rw [colThru_card (L := L) hdeg hxγ]
        ring

end Round

end

end Work.Deep.Kahn

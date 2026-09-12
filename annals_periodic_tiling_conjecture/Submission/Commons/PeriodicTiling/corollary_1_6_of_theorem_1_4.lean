import Mathlib
import Submission.Commons.PeriodicTiling.quotient_aperiodic_tiling_equation_lift_of_zero
import Submission.Commons.PeriodicTiling.IsAperiodicTilingEquation_map_addEquiv

open Filter
open scoped Pointwise

namespace Commons.PeriodicTiling

/-! Helper lemmas for Corollary 1.6 of Theorem 1.4.
These lemmas work with the `PeriodicTilingConjecture` definitions from `ChallengeDeps`. -/

/-- Every finite abelian group admits a surjective homomorphism from `Fin n → ℤ`. -/
lemma exists_surjective_addMonoidHom_fin_of_fintype (G : Type*) [AddCommGroup G] [Fintype G] :
    ∃ (π : (Fin (Fintype.card G) → ℤ) →+ G), Function.Surjective π := by
  classical
  let e : Fin (Fintype.card G) ≃ G := (Fintype.equivFin G).symm
  let π : (Fin (Fintype.card G) → ℤ) →+ G :=
  { toFun := fun v => ∑ i : Fin (Fintype.card G), v i • e i
    map_zero' := by simp
    map_add' := by
      intro v w
      simp [Finset.sum_add_distrib, add_zsmul] }
  refine ⟨π, ?_⟩
  intro g
  let v : Fin (Fintype.card G) → ℤ := fun i => if e i = g then 1 else 0
  refine ⟨v, ?_⟩
  have hsum : (Finset.univ.sum fun i : Fin (Fintype.card G) =>
      (if e i = g then (1:ℤ) else 0) • e i) = g := by
    convert Finset.sum_eq_single_of_mem (s := (Finset.univ : Finset (Fin (Fintype.card G))))
      (f := fun i : Fin (Fintype.card G) => (if e i = g then (1:ℤ) else 0) • e i)
      (e.symm g) (Finset.mem_univ _) ?_ using 1
    · simp [e]
    · intro b _ hb
      by_cases h : e b = g
      · have : b = e.symm g := by
          apply e.injective
          simpa [e] using h
        exact (hb this).elim
      · simp [h]
  simpa [π, v] using hsum

/-- The additive equivalence between `(Fin m → ℤ) × (Fin n → ℤ)` and `Fin (m+n) → ℤ`. -/
def finProdArrowAddEquiv (m n : ℕ) : ((Fin m → ℤ) × (Fin n → ℤ)) ≃+ (Fin (m+n) → ℤ) where
  toEquiv := (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) ℤ).symm.trans
    (finSumFinEquiv.arrowCongr (Equiv.refl ℤ))
  map_add' := by
    intro p q
    ext i
    cases i using Fin.addCases with
    | left i => simp [Equiv.trans_apply, Equiv.sumArrowEquivProdArrow, finSumFinEquiv]
    | right i => simp [Equiv.trans_apply, Equiv.sumArrowEquivProdArrow, finSumFinEquiv]

/-- Transfer of tilings along an additive equivalence. -/
lemma isTiling_addEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) {F A : Set G} (h : IsTiling F A) :
    IsTiling (e '' F) (e '' A) := by
  classical
  let φA : A ≃ e '' A := e.toEquiv.image A
  let φF : F ≃ e '' F := e.toEquiv.image F
  let φ : A × F ≃ (e '' A) × (e '' F) := φA.prodCongr φF
  have hcomm : (fun x : (e '' A) × (e '' F) => (x.1 : H) + (x.2 : H)) ∘ φ =
      e ∘ (fun x : A × F => (x.1 : G) + (x.2 : G)) := by
    funext x
    rcases x with ⟨a, f⟩
    simp [φ, φA, φF, Equiv.prodCongr_apply, Equiv.image]
  have hbi : Function.Bijective (fun x : A × F => (x.1 : G) + (x.2 : G)) := by
    simpa [IsTiling, AddSubgroup.IsComplement] using h
  have hcomp : Function.Bijective ((fun x : (e '' A) × (e '' F) => (x.1 : H) + (x.2 : H)) ∘ φ) := by
    simpa [hcomm] using e.bijective.comp hbi
  have hfinal : Function.Bijective (fun x : (e '' A) × (e '' F) => (x.1 : H) + (x.2 : H)) := by
    have hcomp' := hcomp.comp φ.symm.bijective
    convert hcomp' using 1
    funext y
    simp [φ]
  simpa [IsTiling, AddSubgroup.IsComplement] using hfinal

/-- Transfer of periodic tiling sets along an additive equivalence. -/
lemma isPeriodicTilingSet_addEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) {A : Set G} (h : IsPeriodicTilingSet A) :
    IsPeriodicTilingSet (e '' A) := by
  classical
  rcases h with ⟨L, hLfin, s, rfl⟩
  let L' : AddSubgroup H := L.map e.toAddMonoidHom
  have hL'fin : L'.FiniteIndex := by
    have hrel : L.relIndex ⊤ ≠ 0 := by
      rw [AddSubgroup.relIndex_top_right]
      exact hLfin.index_ne_zero
    have hc := AddSubgroup.relIndex_comap_ne_zero (G := H) (G' := G)
      (f := e.symm.toAddMonoidHom) (J := L) (K := ⊤) hrel
    have hL'eq : L' = L.comap e.symm.toAddMonoidHom := by
      ext x
      simp [L', AddSubgroup.mem_map, AddSubgroup.mem_comap]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        refine ⟨e.symm x, hx, ?_⟩
        simp
    exact ⟨by simpa [hL'eq, AddSubgroup.relIndex_top_right] using hc⟩
  refine ⟨L', hL'fin, s.image e, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_add] at hx
    rcases hx with ⟨a, ha, b, hb, hx⟩
    rw [Set.mem_add]
    refine ⟨e a, ?_, e b, ?_, ?_⟩
    · rw [Finset.mem_coe]
      exact Finset.mem_image.mpr ⟨a, by simpa [Finset.mem_coe] using ha, rfl⟩
    · exact AddSubgroup.mem_map.mpr ⟨b, by simpa using hb, rfl⟩
    · simpa [← map_add] using congrArg e hx
  · intro hy
    rw [Set.mem_add] at hy
    rcases hy with ⟨a, ha, b, hb, hy⟩
    rw [Finset.mem_coe, Finset.mem_image] at ha
    rcases ha with ⟨a0, ha0, rfl⟩
    rcases AddSubgroup.mem_map.mp hb with ⟨b0, hb0, rfl⟩
    rw [Set.mem_image]
    refine ⟨a0 + b0, ?_, by simpa [map_add] using hy⟩
    rw [Set.mem_add]
    exact ⟨a0, by simpa [Finset.mem_coe] using ha0, b0, by simpa using hb0, rfl⟩

/-- Transfer of aperiodic tiling equations along an additive equivalence. -/
lemma isAperiodicTilingEquation_addEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) {F : Set G} (hF : IsAperiodicTilingEquation F) :
    IsAperiodicTilingEquation (e '' F) := by
  classical
  refine ⟨?_, ?_⟩
  · rcases hF.solvable with ⟨A, hA⟩
    exact ⟨e '' A, isTiling_addEquiv e hA⟩
  · intro B hB hBper
    let A : Set G := e.symm '' B
    have hA_tile : IsTiling F A := by
      have htmp := isTiling_addEquiv (e := e.symm) (F := e '' F) (A := B) hB
      have hpre : e.symm '' (e '' F) = F := by
        ext x
        simp [e.symm_apply_apply]
      simpa [A, hpre] using htmp
    have hA_per : IsPeriodicTilingSet A := isPeriodicTilingSet_addEquiv (e := e.symm) hBper
    exact hF.aperiodic A hA_tile hA_per

/-- Characterisation of membership in `s + L` in a product, in the zero fiber. -/
lemma fiber_zero_mem_add_iff {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (s : Finset (G × H)) (L : AddSubgroup (G × H)) (g : G) :
    (g, 0) ∈ (s : Set (G × H)) + L ↔ ∃ t ∈ s, ∃ l ∈ L, t + l = (g, 0) := by
  rw [Set.mem_add]
  simp

/-- The zero fiber of a periodic set in a product is periodic. -/
lemma fiber_zero_periodic_of_periodic {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {B : Set (G × H)} (hBper : IsPeriodicTilingSet B) :
    IsPeriodicTilingSet {g : G | (g, 0) ∈ B} := by
  classical
  rcases hBper with ⟨L, hLfin, s, rfl⟩
  let L0 : AddSubgroup G := L.comap (AddMonoidHom.inl G H)
  have hL0fin : L0.FiniteIndex := by
    have hrel : L.relIndex ⊤ ≠ 0 := by
      rw [AddSubgroup.relIndex_top_right]
      exact hLfin.index_ne_zero
    have hcomap := AddSubgroup.relIndex_comap_ne_zero (G := G) (G' := G × H)
      (f := AddMonoidHom.inl G H) (J := L) (K := ⊤) hrel
    exact ⟨by simpa [L0, AddSubgroup.relIndex_top_right] using hcomap⟩
  let hasRep (t : G × H) : Prop := ∃ g : G, (g, 0) ∈ (({t} : Finset (G × H)) : Set (G × H)) + L
  let rep (t : G × H) : G := if h : hasRep t then Classical.choose h else 0
  let s0 : Finset G := (s.filter (fun t => hasRep t)).image rep
  refine ⟨L0, hL0fin, s0, ?_⟩
  ext g
  constructor
  · intro hg
    have hg' : (g, 0) ∈ (s : Set (G × H)) + L := by simpa using hg
    rw [fiber_zero_mem_add_iff] at hg'
    rcases hg' with ⟨t, ht, l, hl, hsum⟩
    have htrep : hasRep t := ⟨g, by
      rw [fiber_zero_mem_add_iff]
      exact ⟨t, by simp, l, hl, hsum⟩⟩
    have ht_in_filter : t ∈ s.filter (fun t => hasRep t) := by
      simp [ht, htrep]
    have hrep_mem : rep t ∈ s0 := by
      exact Finset.mem_image.mpr ⟨t, ht_in_filter, rfl⟩
    have hrep : (rep t, 0) ∈ (({t} : Finset (G × H)) : Set (G × H)) + L := by
      dsimp [rep]
      rw [dif_pos htrep]
      exact Classical.choose_spec htrep
    rw [fiber_zero_mem_add_iff] at hrep
    rcases hrep with ⟨t', ht', l', hl', hsum'⟩
    have ht' : t' = t := by simpa using ht'
    subst t'
    have hdiff : (g - rep t, 0) ∈ L := by
      have hdiff' : (g, 0) - (rep t, 0) ∈ L := by
        have h1 : (g, 0) - (rep t, 0) = l - l' := by
          calc
            (g, 0) - (rep t, 0) = (t + l) - (t + l') := by rw [← hsum, ← hsum']
            _ = l - l' := by abel
        rw [h1]
        exact L.sub_mem hl hl'
      simpa using hdiff'
    have hmemL0 : g - rep t ∈ L0 := by
      simpa [L0, AddSubgroup.mem_comap] using hdiff
    have hsumG : g = rep t + (g - rep t) := by abel
    rw [hsumG]
    exact Set.add_mem_add hrep_mem hmemL0
  · intro hg
    have hg' : g ∈ (s0 : Set G) + L0 := by simpa using hg
    rw [Set.mem_add] at hg'
    rcases hg' with ⟨a, ha, b, hb, hsum⟩
    rcases Finset.mem_image.mp ha with ⟨t, ht, rfl⟩
    have htfilter : t ∈ s.filter (fun t => hasRep t) := ht
    have ht : t ∈ s := by simpa using (Finset.mem_filter.mp htfilter).1
    have htrep : hasRep t := by simpa using (Finset.mem_filter.mp htfilter).2
    have hrep : (rep t, 0) ∈ (({t} : Finset (G × H)) : Set (G × H)) + L := by
      dsimp [rep]
      rw [dif_pos htrep]
      exact Classical.choose_spec htrep
    rw [fiber_zero_mem_add_iff] at hrep
    rcases hrep with ⟨t', ht', l', hl', hsum'⟩
    have ht' : t' = t := by simpa using ht'
    subst t'
    have hbL0 : b ∈ L0 := hb
    have hb_prod : (b, 0) ∈ L := by
      simpa [L0, AddSubgroup.mem_comap] using hbL0
    have hsumG : rep t + b = g := hsum
    change (g, 0) ∈ (s : Set (G × H)) + L
    rw [fiber_zero_mem_add_iff]
    refine ⟨t, ht, l' + (b, 0), L.add_mem hl' hb_prod, ?_⟩
    calc
      t + (l' + (b, 0)) = (t + l') + (b, 0) := by abel
      _ = (rep t, 0) + (b, 0) := by rw [hsum']
      _ = (rep t + b, 0) := by simp
      _ = (g, 0) := by rw [← hsumG]

/-- If `F × {0}` tiles a product with `B`, then the zero fiber of `B` tiles `G` with `F`. -/
lemma fiber_zero_tiling_of_prod_zero_tiling {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {F : Set G} {B : Set (G × H)}
    (hB : IsTiling (F ×ˢ ({0} : Set H)) B) :
    IsTiling F {g : G | (g, 0) ∈ B} := by
  classical
  rw [IsTiling, AddSubgroup.IsComplement]
  constructor
  · rintro ⟨⟨b1, hb1B0⟩, ⟨f1, hf1F⟩⟩ ⟨⟨b2, hb2B0⟩, ⟨f2, hf2F⟩⟩ hsum
    have hb1' : (b1, 0) ∈ B := by simpa using hb1B0
    have hb2' : (b2, 0) ∈ B := by simpa using hb2B0
    have hf1' : (f1, 0) ∈ F ×ˢ ({0} : Set H) := ⟨hf1F, rfl⟩
    have hf2' : (f2, 0) ∈ F ×ˢ ({0} : Set H) := ⟨hf2F, rfl⟩
    have hprod_sum : (fun x : B × (F ×ˢ ({0} : Set H)) => x.1.1 + x.2.1)
        (⟨(b1, 0), hb1'⟩, ⟨(f1, 0), hf1'⟩) =
        (fun x : B × (F ×ˢ ({0} : Set H)) => x.1.1 + x.2.1)
        (⟨(b2, 0), hb2'⟩, ⟨(f2, 0), hf2'⟩) := by
      change (b1, 0) + (f1, 0) = (b2, 0) + (f2, 0)
      ext <;> simp [hsum]
    have hpair := hB.1 (a₁ := (⟨(b1, 0), hb1'⟩, ⟨(f1, 0), hf1'⟩))
      (a₂ := (⟨(b2, 0), hb2'⟩, ⟨(f2, 0), hf2'⟩)) hprod_sum
    have hb : b1 = b2 := by
      have := congrArg (fun x : B × (F ×ˢ ({0} : Set H)) => (x.1 : G × H).1) hpair
      simpa using this
    have hf : f1 = f2 := by
      have := congrArg (fun x : B × (F ×ˢ ({0} : Set H)) => (x.2 : G × H).1) hpair
      simpa using this
    exact Prod.ext (Subtype.ext hb) (Subtype.ext hf)
  · intro g
    obtain ⟨x, hx⟩ := hB.2 (g, 0)
    let b : G × H := x.1.1
    let f : G × H := x.2.1
    have hb : b ∈ B := x.1.2
    have hf : f ∈ F ×ˢ ({0} : Set H) := x.2.2
    have hsum : b + f = (g, 0) := hx
    rcases Set.mem_prod.mp hf with ⟨hf1, hf2⟩
    have hsum1 : b.1 + f.1 = g := by
      have := congrArg (fun y : G × H => y.1) hsum
      simpa using this
    have hsum2 : b.2 + f.2 = 0 := by
      have := congrArg (fun y : G × H => y.2) hsum
      simpa using this
    have hb2 : b.2 = 0 := by
      rw [hf2] at hsum2
      simpa using hsum2
    have hb0 : (b.1, 0) ∈ B := by
      convert hb using 1
      ext <;> simp [hb2]
    refine ⟨(⟨b.1, hb0⟩, ⟨f.1, hf1⟩), ?_⟩
    simpa [hsum1]

/-- Extending an aperiodic tiling equation by a zero tile in a product. -/
lemma prod_zero_aperiodic {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {F : Set G} (hF : IsAperiodicTilingEquation F) :
    IsAperiodicTilingEquation (F ×ˢ ({0} : Set H)) where
  solvable := by
    rcases hF.solvable with ⟨A, hA⟩
    refine ⟨A ×ˢ (Set.univ : Set H), ?_⟩
    rw [IsTiling, AddSubgroup.IsComplement]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨f, hf⟩⟩ ⟨⟨a', ha'⟩, ⟨f', hf'⟩⟩ hsum
      have haA : a.1 ∈ A := (Set.mem_prod.mp ha).1
      have ha'A : a'.1 ∈ A := (Set.mem_prod.mp ha').1
      have hfF : f.1 ∈ F := (Set.mem_prod.mp hf).1
      have hf'F : f'.1 ∈ F := (Set.mem_prod.mp hf').1
      have hsumG : a.1 + f.1 = a'.1 + f'.1 := by
        have := congrArg (fun y : G × H => y.1) hsum
        simpa using this
      have hpair := hA.1 (a₁ := (⟨a.1, haA⟩, ⟨f.1, hfF⟩)) (a₂ := (⟨a'.1, ha'A⟩, ⟨f'.1, hf'F⟩)) hsumG
      have haeq : a = a' := by
        apply Prod.ext
        · exact congrArg (fun x : A × F => (x.1 : G)) hpair
        · have hsumH : a.2 + f.2 = a'.2 + f'.2 := by
            have := congrArg (fun y : G × H => y.2) hsum
            simpa using this
          have hf2 : f.2 = 0 := (Set.mem_prod.mp hf).2
          have hf'2 : f'.2 = 0 := (Set.mem_prod.mp hf').2
          simpa [hf2, hf'2] using hsumH
      have hfeq : f = f' := by
        apply Prod.ext
        · exact congrArg (fun x : A × F => (x.2 : G)) hpair
        · have hf2 : f.2 = 0 := (Set.mem_prod.mp hf).2
          have hf'2 : f'.2 = 0 := (Set.mem_prod.mp hf').2
          rw [hf2, hf'2]
      exact Prod.ext (Subtype.ext haeq) (Subtype.ext hfeq)
    · intro x
      obtain ⟨pair, hpair⟩ := hA.2 x.1
      let a : G := pair.1.1
      let f : G := pair.2.1
      have ha : a ∈ A := pair.1.2
      have hf : f ∈ F := pair.2.2
      have hsumG : a + f = x.1 := hpair
      refine ⟨(⟨(a, x.2), ⟨ha, trivial⟩⟩, ⟨(f, 0), ⟨hf, rfl⟩⟩), ?_⟩
      ext <;> simp [hsumG]
  aperiodic := by
    intro B hB hBper
    have hB0tile : IsTiling F {g : G | (g, 0) ∈ B} := fiber_zero_tiling_of_prod_zero_tiling hB
    have hB0per : IsPeriodicTilingSet {g : G | (g, 0) ∈ B} := fiber_zero_periodic_of_periodic hBper
    exact hF.aperiodic {g : G | (g, 0) ∈ B} hB0tile hB0per

/-- Translate the tile by `-t` and the tiling set by `+t`. -/
lemma isTiling_sub_add {G : Type*} [AddCommGroup G] {F A : Set G}
    (h : IsTiling F A) (t : G) :
    IsTiling (Set.image (fun x : G => x - t) F) (A + {t}) := by
  classical
  rw [IsTiling, AddSubgroup.isComplement_iff_existsUnique]
  intro g
  obtain ⟨p, hp, huniq⟩ := AddSubgroup.IsComplement.existsUnique (S := A) (T := F) h g
  let a : G := p.1.1
  let f : G := p.2.1
  refine ⟨(⟨a + t, by
      rw [Set.mem_add]
      exact ⟨a, p.1.2, t, by simp, rfl⟩⟩,
      ⟨f - t, by
        refine ⟨f, p.2.2, ?_⟩
        simp⟩), ?_, ?_⟩
  · have hsum : a + f = g := hp
    have hsum' : (a + t) + (f - t) = g := by
      calc
        (a + t) + (f - t) = a + f := by abel
        _ = g := hsum
    simpa using hsum'
  · rintro y hy
    rcases y with ⟨⟨a', ha'⟩, ⟨f', hf'⟩⟩
    have hsum' : (a' : G) + (f' : G) = g := hy
    rcases Set.mem_add.mp ha' with ⟨a0, ha0, t0, ht0, ha0eq⟩
    have ht0' : t0 = t := by simpa using ht0
    subst t0
    rcases hf' with ⟨f0, hf0, hf0eq⟩
    have hcore : a0 + f0 = g := by
      calc
        a0 + f0 = (a0 + t) + (f0 - t) := by abel
        _ = (a' : G) + (f' : G) := by rw [← ha0eq, ← hf0eq]
        _ = g := hsum'
    have hpair : (⟨a0, ha0⟩, ⟨f0, hf0⟩) = p := huniq (⟨a0, ha0⟩, ⟨f0, hf0⟩) hcore
    have ha0eq_final : a0 = a := by
      have := congrArg (fun x : A × F => (x.1 : G)) hpair
      simpa [a] using this
    have hf0eq_final : f0 = f := by
      have := congrArg (fun x : A × F => (x.2 : G)) hpair
      simpa [f] using this
    apply Prod.ext
    · apply Subtype.ext
      simpa [ha0eq_final] using ha0eq.symm
    · apply Subtype.ext
      simpa [hf0eq_final] using hf0eq.symm

/-- Translating a periodic tiling set by an element keeps it periodic. -/
lemma isPeriodicTilingSet_add {G : Type*} [AddCommGroup G] {A : Set G}
    (h : IsPeriodicTilingSet A) (t : G) :
    IsPeriodicTilingSet (A + {t}) := by
  classical
  rcases h with ⟨H, hHfin, s, hs⟩
  refine ⟨H, hHfin, s.image (fun a => a + t), ?_⟩
  ext x
  constructor
  · intro hx
    rw [Set.mem_add] at hx ⊢
    rcases hx with ⟨a, ha, b, hb, hsum⟩
    have hb' : b = t := Set.mem_singleton_iff.mp hb
    subst b
    have haA : a ∈ (s : Set G) + H := by simpa [hs] using ha
    rw [Set.mem_add] at haA
    rcases haA with ⟨u, hu, h, hh, ha_eq⟩
    refine ⟨u + t, ?_, h, hh, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, by simpa [Finset.mem_coe] using hu, rfl⟩
    · calc
        u + t + h = u + h + t := by abel
        _ = a + t := by rw [ha_eq]
        _ = x := hsum
  · intro hx
    rw [Set.mem_add] at hx ⊢
    rcases hx with ⟨a, ha, h, hh, hsum⟩
    rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
    refine ⟨u + h, ?_, t, by simp, ?_⟩
    · rw [hs]
      exact Set.add_mem_add (by simpa [Finset.mem_coe] using hu) hh
    · calc
        u + h + t = u + t + h := by abel
        _ = x := hsum

/-- Translate a finite nonempty aperiodic set so that it contains zero. -/
lemma translate_to_zero {G : Type*} [AddCommGroup G]
    {F : Set G} (hFfin : F.Finite) (hFne : F.Nonempty)
    (hF : IsAperiodicTilingEquation F) :
    ∃ F₀ : Set G, F₀.Finite ∧ (0 : G) ∈ F₀ ∧ IsAperiodicTilingEquation F₀ := by
  classical
  rcases hFne with ⟨f₀, hf₀⟩
  let F₀ : Set G := Set.image (fun x : G => x - f₀) F
  have hF₀fin : F₀.Finite := hFfin.image _
  have hF₀zero : (0 : G) ∈ F₀ := by
    refine ⟨f₀, hf₀, ?_⟩
    simp
  refine ⟨F₀, hF₀fin, hF₀zero, ?_⟩
  refine ⟨?_, ?_⟩
  · rcases hF.solvable with ⟨A, hA⟩
    refine ⟨A + {f₀}, ?_⟩
    exact isTiling_sub_add (F := F) (A := A) hA f₀
  · intro B hB hBper
    have hAtile : IsTiling F (B + {-f₀}) := by
      have hsub := isTiling_sub_add (F := F₀) (A := B) hB (-f₀)
      have hpre : Set.image (fun x : G => x + f₀) F₀ = F := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rcases hy with ⟨z, hz, rfl⟩
          simpa using hz
        · intro hx
          refine ⟨x - f₀, ⟨x, hx, ?_⟩, ?_⟩
          · abel
          · abel
      simpa [F₀, hpre] using hsub
    have hAper : IsPeriodicTilingSet (B + {-f₀}) := isPeriodicTilingSet_add hBper (-f₀)
    exact hF.aperiodic (B + {-f₀}) hAtile hAper


/-- Corollary 1.6 of the paper, derived from Theorem 1.4. -/
theorem corollary_1_6_of_theorem_1_4
    (h14 : ∃ (G₀ : Type) (_ : AddCommGroup G₀) (_ : Finite G₀),
      ∃ F : Set (ℤ × ℤ × G₀), F.Finite ∧ F.Nonempty ∧ IsAperiodicTilingEquation F) :
    ∀ᶠ d in atTop, ∃ (F : Set (Fin d → ℤ)),
      F.Finite ∧ F.Nonempty ∧ IsAperiodicTilingEquation F := by
  classical
  rcases h14 with ⟨G₀, hG₀add, hG₀fin, F, hFfin, hFne, hF⟩
  letI : AddCommGroup G₀ := hG₀add
  letI : Finite G₀ := hG₀fin
  letI : Fintype G₀ := Fintype.ofFinite G₀
  let G : Type := ℤ × ℤ × G₀
  letI : AddCommGroup G := inferInstance
  obtain ⟨F₀, hF₀fin, hF₀zero, hF₀ap⟩ :=
    translate_to_zero (G := G) hFfin hFne hF
  let n : ℕ := Fintype.card G₀
  obtain ⟨πG, hπG⟩ :=
    exists_surjective_addMonoidHom_fin_of_fintype (G := G₀)
  let πprod : ((Fin 2 → ℤ) × (Fin n → ℤ)) →+ (ℤ × ℤ × G₀) :=
  { toFun := fun p => (p.1 0, p.1 1, πG p.2)
    map_zero' := by simp [πG.map_zero]
    map_add' := by
      intro p q
      ext <;> simp [πG.map_add] }
  have hπprod : Function.Surjective πprod := by
    intro g
    rcases g with ⟨a, b, c⟩
    rcases hπG c with ⟨w, hw⟩
    let v : Fin 2 → ℤ := ![a, b]
    refine ⟨(v, w), ?_⟩
    change ((v 0, v 1, πG w) = (a, b, c))
    simp [v, hw]
  let eA : ((Fin 2 → ℤ) × (Fin n → ℤ)) ≃+ (Fin (2 + n) → ℤ) :=
    finProdArrowAddEquiv 2 n
  let πfin : (Fin (2 + n) → ℤ) →+ (ℤ × ℤ × G₀) :=
    πprod.comp eA.symm.toAddMonoidHom
  have hπfin : Function.Surjective πfin := by
    intro g
    obtain ⟨p, hp⟩ := hπprod g
    refine ⟨eA p, ?_⟩
    simpa [πfin] using hp
  let N : ℕ := 2 + n
  obtain ⟨Fbase, hFbasefin, hFbasene, hFbaseap⟩ :=
    quotient_aperiodic_tiling_equation_lift_of_zero
      (G := G) (d := N) (π := πfin) (hπ := hπfin) (F := F₀)
      hF₀fin hF₀zero hF₀ap
  -- eventually: for every d ≥ N
  rw [eventually_atTop]
  refine ⟨N, ?_⟩
  intro d hd
  let r : ℕ := d - N
  have hNr : N + r = d := Nat.add_sub_of_le hd
  let eAdd : ((Fin N → ℤ) × (Fin r → ℤ)) ≃+ (Fin d → ℤ) :=
    (finProdArrowAddEquiv N r).trans
      (AddEquiv.cast (M := fun k : ℕ => Fin k → ℤ) (by omega))
  let Fprod : Set ((Fin N → ℤ) × (Fin r → ℤ)) := Fbase ×ˢ ({0} : Set (Fin r → ℤ))
  have hFprodfin : Fprod.Finite := hFbasefin.prod (Set.finite_singleton 0)
  have hFprodne : Fprod.Nonempty := hFbasene.prod (Set.singleton_nonempty 0)
  have hFprodap : IsAperiodicTilingEquation Fprod :=
    prod_zero_aperiodic (G := Fin N → ℤ) (H := Fin r → ℤ) hFbaseap
  let Fd : Set (Fin d → ℤ) := eAdd '' Fprod
  refine ⟨Fd, ?_, ?_, ?_⟩
  · exact hFprodfin.image _
  · exact hFprodne.image _
  · exact isAperiodicTilingEquation_addEquiv eAdd hFprodap

end Commons.PeriodicTiling

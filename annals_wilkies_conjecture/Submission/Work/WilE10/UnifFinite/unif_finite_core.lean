/-
  `E0b`-core: uniform finiteness of the fibres of an `rexp`-existential family, from the
  Binyamini–Vorobjov sharp cell decomposition (`E7_prop_main`), the compactification `psi`
  (whose coordinatewise map `psiV` is a bijection `ℝⁿ ≃ (-1,1)ⁿ`) and the transport of
  `rexp`-existential sets to sub-Pfaffian sets (`E10_rexp_to_subpf`).

  The mathematics of the proof.

  Let `Y ⊆ ℝ^{k+1}` be `rexp`-existential. Then `Y = psiV ⁻¹' Z` for a sub-Pfaffian `Z`, and
  `Z = projFirst (k+1) m '' X.set` for a semi-Pfaffian `X` in `ℝ^{(k+1)+m}`. We want a bound,
  uniform in `c : Fin k → ℝ`, on the number of pieces of the fibre

      `{t | Fin.cons t c ∈ Y}`.

  The fibre direction is the *first* coordinate, whereas the cylindrical decomposition of
  `Z` given by `E7_prop_main` is aligned with the *last* coordinate. So we first reindex
  `ℝ^{k+1}` by the rotation `rot k` of `Fin (k+1)` (the inverse of `finRotate (k+1)`), which
  moves the first coordinate to the last one; the reindexed family is obtained from `X` by
  the block rotation `pp k m` of the coordinates of `ℝ^{(k+1)+m}`, and the generic vocabulary
  `toSemiPf` of `WilE10/Vocab.lean` performs that transport.

  A cylindrical decomposition `C` of `cubeC (k+1)` compatible with the reindexed `Z'` has
  cells whose fibres over any base point are a point or an interval (hence `OrdConnected`),
  and `Z'` is the union of the cells contained in it. Applying `psi` we get the desired
  decomposition: `psi` is (strictly) increasing, so the preimage of each `OrdConnected` piece
  is again `OrdConnected`, hence `IsPreconnected`, and the number of pieces is at most the
  number of cells, which `E7_prop_main` bounds by a function of the format and degree of `X`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilE10.Vocab
import Submission.Work.WilE9.Psi.hasDerivAt_psi
import Submission.Work.WilE9.Psi.psig_pos

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10.UnifFinite

open WilkiesDesign WilkiesDesign.E

/-! ## The rotation of the first `k+1` coordinates -/

/-- The rotation `i ↦ i - 1` of `Fin (k+1)`: it moves `0` to the last coordinate, which is the
direction of the cylindrical decomposition. -/
def rot (k : ℕ) : Fin (k+1) ≃ Fin (k+1) := (finRotate (k+1)).symm

/-- The rotation `i ↦ i - 1` extended to `Fin ((k+1)+m)` by the identity on the last `m`
coordinates. -/
def pp (k m : ℕ) : Fin ((k+1)+m) ≃ Fin ((k+1)+m) :=
  (finSumFinEquiv (m := k+1) (n := m)).symm.trans
    ((Equiv.sumCongr (rot k) (Equiv.refl (Fin m))).trans
      (finSumFinEquiv (m := k+1) (n := m)))

/-- The transport of a subset of `ℝ^{k+1}` along the rotation `rot k`. -/
abbrev rotSet {k : ℕ} (Z : Set (Fin (k+1) → ℝ)) : Set (Fin (k+1) → ℝ) := {v | v ∘ ⇑(rot k) ∈ Z}

theorem pp_castAdd (k m : ℕ) (i : Fin (k+1)) :
    pp k m (Fin.castAdd m i) = Fin.castAdd m (rot k i) := by
  simp only [pp, Equiv.trans_apply, Equiv.sumCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    Sum.map_inl, finSumFinEquiv_apply_left]

theorem pp_natAdd (k m : ℕ) (j : Fin m) :
    pp k m (Fin.natAdd (k+1) j) = Fin.natAdd (k+1) j := by
  simp only [pp, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
    finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, finSumFinEquiv_apply_right]

theorem pp_symm_castAdd (k m : ℕ) (i : Fin (k+1)) :
    (pp k m).symm (Fin.castAdd m i) = Fin.castAdd m ((rot k).symm i) := by
  have h : pp k m (Fin.castAdd m ((rot k).symm i)) = Fin.castAdd m i := by
    rw [pp_castAdd]
    exact congrArg (Fin.castAdd m) (Equiv.apply_symm_apply (rot k) i)
  rw [← h, Equiv.symm_apply_apply]

/-- Projection commutes with the rotation of the block. -/
theorem projFirst_comp_pp {k m : ℕ} (y : Fin ((k+1)+m) → ℝ) :
    projFirst (k+1) m (y ∘ ⇑(pp k m)) = (projFirst (k+1) m y) ∘ ⇑(rot k) := by
  funext i
  simp only [Function.comp_apply, projFirst, pp_castAdd]

/-- Projection commutes with the inverse rotation of the block. -/
theorem projFirst_comp_pp_symm {k m : ℕ} (y : Fin ((k+1)+m) → ℝ) :
    projFirst (k+1) m (y ∘ ⇑(pp k m).symm) = (projFirst (k+1) m y) ∘ ⇑(rot k).symm := by
  funext i
  simp only [Function.comp_apply, projFirst, pp_symm_castAdd]

/-- The rotation identifies the last coordinate with the first one: `Fin.snoc` becomes
`Fin.cons`. -/
theorem snoc_comp_rot {k : ℕ} (c : Fin k → ℝ) (u : ℝ) :
    (Fin.snoc c u) ∘ ⇑(rot k) = Fin.cons u c := by
  funext j
  simp only [Function.comp_apply, rot]
  rw [Fin.snoc_eq_cons_rotate]
  simp

/-- The projection of the rotated family is the rotation of the projection. -/
theorem projFirst_reindex {k m : ℕ} (A : Set (Fin ((k+1)+m) → ℝ)) :
    projFirst (k+1) m '' {y : Fin ((k+1)+m) → ℝ | y ∘ ⇑(pp k m) ∈ A} =
      rotSet (projFirst (k+1) m '' A) := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y ∘ ⇑(pp k m), hy, projFirst_comp_pp y⟩
  · rintro ⟨u, hu, hv⟩
    refine ⟨u ∘ ⇑(pp k m).symm, ?_, ?_⟩
    · have hcomp : (u ∘ ⇑(pp k m).symm) ∘ ⇑(pp k m) = u := by
        funext i; simp
      change (u ∘ ⇑(pp k m).symm) ∘ ⇑(pp k m) ∈ A
      rw [hcomp]; exact hu
    · rw [projFirst_comp_pp_symm, hv]
      funext i
      simp

/-! ## Elementary facts about the vocabulary -/

/-- A semi-Pfaffian set lies in the cube. -/
theorem semiPf_subset_cube {k : ℕ} (X : SemiPf k) : X.set ⊆ cubeC k := fun _ hx => hx.1

/-- A projection of a point of the cube lies in the cube. -/
theorem projFirst_cube {n m : ℕ} {x : Fin (n+m) → ℝ} (hx : x ∈ cubeC (n+m)) :
    projFirst n m x ∈ cubeC n := fun i => hx _

/-- `psi` is strictly increasing: this is the only analytic input of the proof. -/
theorem strictMono_psi : StrictMono (psi : ℝ → ℝ) :=
  strictMono_of_hasDerivAt_pos (fun x => Work.WilE9.Psi.hasDerivAt_psi x)
    (fun x => pow_pos (Work.WilE9.Psi.psig_pos x) 3)

/-- `psiV` commutes with `Fin.cons`/`Fin.tail`. -/
theorem psiV_cons {k : ℕ} (t : ℝ) (c : Fin k → ℝ) :
    psiV (Fin.cons t c) = Fin.cons (psi t) (psiV c) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [psiV]
  · intro j; simp [psiV]

/-! ## The generic-index-type vocabulary -/

/-- View a semi-Pfaffian set over `Fin K` as one over the generic index type `Fin K`. -/
def toI {K : ℕ} (X : SemiPf K) : SemiPfI (Fin K) :=
  ⟨X.r, ⟨X.c.a, X.c.b⟩, X.basics.map (fun B => (⟨B.eqs, B.pos⟩ : BasicI (Fin K) X.r))⟩

theorem toI_set {K : ℕ} (X : SemiPf K) : (toI X).set = X.set := by
  ext x
  constructor
  · rintro ⟨h1, B, hB, hBh⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    exact ⟨h1, B₀, hB₀, hBh⟩
  · rintro ⟨h1, B₀, hB₀, hBh⟩
    exact ⟨h1, ⟨B₀.eqs, B₀.pos⟩, List.mem_map_of_mem hB₀, hBh⟩

/-! ## Fibres of cells are intervals -/

theorem fib_graph {k : ℕ} (C : Set (Fin k → ℝ)) (f : (Fin k → ℝ) → ℝ) (c : Fin k → ℝ) :
    Set.OrdConnected {u : ℝ | Fin.snoc c u ∈ {z : Fin (k+1) → ℝ |
      Fin.init z ∈ C ∧ z (Fin.last k) = f (Fin.init z)}} := by
  by_cases hc : c ∈ C
  · have hset : {u : ℝ | Fin.snoc c u ∈ {z : Fin (k+1) → ℝ |
        Fin.init z ∈ C ∧ z (Fin.last k) = f (Fin.init z)}} = {f c} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      rw [Fin.init_snoc, Fin.snoc_last]
      exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
    rw [hset]; exact Set.ordConnected_singleton
  · have hset : {u : ℝ | Fin.snoc c u ∈ {z : Fin (k+1) → ℝ |
        Fin.init z ∈ C ∧ z (Fin.last k) = f (Fin.init z)}} = ∅ := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [Fin.init_snoc, Fin.snoc_last]
      exact fun h => hc h.1
    rw [hset]; exact Set.ordConnected_empty

theorem fib_band {k : ℕ} (C : Set (Fin k → ℝ)) (a b : (Fin k → ℝ) → EReal) (c : Fin k → ℝ) :
    Set.OrdConnected {u : ℝ | Fin.snoc c u ∈ {z : Fin (k+1) → ℝ |
      Fin.init z ∈ C ∧ a (Fin.init z) < ((z (Fin.last k) : ℝ) : EReal) ∧
        ((z (Fin.last k) : ℝ) : EReal) < b (Fin.init z)}} := by
  by_cases hc : c ∈ C
  · have hset : {u : ℝ | Fin.snoc c u ∈ {z : Fin (k+1) → ℝ |
        Fin.init z ∈ C ∧ a (Fin.init z) < ((z (Fin.last k) : ℝ) : EReal) ∧
          ((z (Fin.last k) : ℝ) : EReal) < b (Fin.init z)}} =
        Real.toEReal ⁻¹' Set.Ioo (a c) (b c) := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioo]
      rw [Fin.init_snoc, Fin.snoc_last]
      exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hc, h.1, h.2⟩⟩
    rw [hset]
    exact Set.ordConnected_Ioo.preimage_mono EReal.coe_strictMono.monotone
  · have hset : {u : ℝ | Fin.snoc c u ∈ {z : Fin (k+1) → ℝ |
        Fin.init z ∈ C ∧ a (Fin.init z) < ((z (Fin.last k) : ℝ) : EReal) ∧
          ((z (Fin.last k) : ℝ) : EReal) < b (Fin.init z)}} = ∅ := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [Fin.init_snoc, Fin.snoc_last]
      exact fun h => hc h.1
    rw [hset]; exact Set.ordConnected_empty

/-- The fibre in the last coordinate direction of a cell is a point or an interval. -/
theorem fib_cell {k : ℕ} {κ : Set (Fin (k+1) → ℝ)} (h : IsCell (k+1) κ) (c : Fin k → ℝ) :
    Set.OrdConnected {u : ℝ | Fin.snoc c u ∈ κ} := by
  cases h with
  | graph => rename_i C hC f hf; exact fib_graph C f c
  | band => rename_i C hC a b ha hb hab; exact fib_band C a b c

/-! ## The fibre count -/

/-- A point of `Z'` is a point of one of the cells of `C` that are contained in `Z'`. -/
theorem mem_iff_exists_cell {k : ℕ} {Z' : Set (Fin (k+1) → ℝ)}
    {C : Finset (Set (Fin (k+1) → ℝ))}
    (hcover : ⋃₀ (C : Set (Set (Fin (k+1) → ℝ))) = cubeC (k+1))
    (hsep : ∀ κ ∈ C, κ ⊆ Z' ∨ Disjoint κ Z') (hsub : Z' ⊆ cubeC (k+1))
    (c : Fin k → ℝ) (u : ℝ) :
    Fin.snoc c u ∈ Z' ↔ ∃ κ ∈ C.filter (fun κ => κ ⊆ Z'), Fin.snoc c u ∈ κ := by
  constructor
  · intro h
    have hmem : Fin.snoc c u ∈ ⋃₀ (C : Set (Set (Fin (k+1) → ℝ))) := by
      rw [hcover]; exact hsub h
    obtain ⟨κ, hκC, hκ⟩ := Set.mem_sUnion.mp hmem
    refine ⟨κ, ?_, hκ⟩
    refine Finset.mem_filter.mpr ⟨hκC, ?_⟩
    rcases hsep κ hκC with hsub' | hdis
    · exact hsub'
    · exact absurd h (Set.disjoint_left.mp hdis hκ)
  · rintro ⟨κ, hκ, hκu⟩
    exact (Finset.mem_filter.mp hκ).2 hκu

/-- Rewriting the fibre of `Y = psiV ⁻¹' Z` in terms of the rotated `Z`: the first coordinate
becomes the last one. -/
theorem cons_mem_iff {k : ℕ} {Z : Set (Fin (k+1) → ℝ)} (c : Fin k → ℝ) (t : ℝ) :
    Fin.cons t c ∈ psiV ⁻¹' Z ↔ Fin.snoc (psiV c) (psi t) ∈ rotSet Z := by
  have h₁ : Fin.cons t c ∈ psiV ⁻¹' Z ↔ Fin.cons (psi t) (psiV c) ∈ Z := by
    rw [Set.mem_preimage, psiV_cons]
  have h₂ : Fin.snoc (psiV c) (psi t) ∈ rotSet Z ↔ Fin.cons (psi t) (psiV c) ∈ Z := by
    simp only [rotSet, Set.mem_ofPred_eq, snoc_comp_rot]
  exact h₁.trans h₂.symm

/-! ## The main theorem -/

theorem unif_finite_core
    (hE7 : ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf (n + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
      ∃ C : Finset (Set (Fin n → ℝ)), WilkiesDesign.E.IsCylDecompOn n (WilkiesDesign.E.cubeC n) C ∧
        (∀ i, ∀ κ ∈ C,
          κ ⊆ WilkiesDesign.E.projFirst n m '' (X i).set ∨
            Disjoint κ (WilkiesDesign.E.projFirst n m '' (X i).set)) ∧
        C.card ≤ MvPolynomial.eval ![D, k] b ∧
        ∀ κ ∈ C, WilkiesDesign.E.Star a (c.eval D) n κ ∧ WilkiesDesign.E.SubPf n κ)
    (hE8 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (D : ℕ) (A : Set (Fin 1 → ℝ)),
      WilkiesDesign.E.Gen F D 1 A →
      ∃ s : Finset (Set (Fin 1 → ℝ)), s.card ≤ p.eval D ∧ (∀ I ∈ s, IsPreconnected I) ∧
        A = ⋃₀ (s : Set (Set (Fin 1 → ℝ))))
    (hE10 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X →
      ∃ Z : Set (Fin n → ℝ), WilkiesDesign.E.SubPf n Z ∧ X = WilkiesDesign.E.psiV ⁻¹' Z) :
    WilkiesDesign.CG.UnifFiniteRExp := by
  intro k Y hY
  obtain ⟨Z, hZsub, hYeq⟩ := hE10 (k + 1) Y hY
  obtain ⟨m, X0, hZeq⟩ := hZsub
  -- the family reindexed by the rotation, so that the fibre direction becomes the last one
  let Xh : SemiPf ((k + 1) + m) := toSemiPf (pp k m) (toI X0)
  have hXh : Xh.set = {y : Fin ((k + 1) + m) → ℝ | y ∘ ⇑(pp k m) ∈ X0.set} := by
    show (toSemiPf (pp k m) (toI X0)).set = _
    rw [toSemiPf_set, toI_set]
  have hproj : projFirst (k + 1) m '' Xh.set = rotSet Z := by
    rw [hXh, hZeq]
    exact projFirst_reindex X0.set
  -- the cylindrical decomposition of BV
  obtain ⟨a, bf, cf, hE7'⟩ := hE7 Xh.fmt (k + 1)
  obtain ⟨C, hCD, hsep0, hcard, _hrest⟩ :=
    hE7' Xh.deg 1 m (fun _ => Xh) (fun _ => ⟨le_refl _, le_refl _⟩)
  obtain ⟨hcells, _hpw, hcover, _hrec⟩ := hCD
  have hsep : ∀ κ ∈ C, κ ⊆ rotSet Z ∨ Disjoint κ (rotSet Z) := by
    intro κ hκ
    have h := hsep0 0 κ hκ
    rwa [hproj] at h
  have hZ'cube : rotSet Z ⊆ cubeC (k + 1) := by
    rw [← hproj]
    rintro v ⟨y, hy, rfl⟩
    exact projFirst_cube (semiPf_subset_cube Xh hy)
  refine ⟨MvPolynomial.eval ![Xh.deg, 1] bf, fun c => ?_⟩
  refine ⟨(C.filter (fun κ => κ ⊆ rotSet Z)).image
      (fun κ => psi ⁻¹' {u : ℝ | Fin.snoc (psiV c) u ∈ κ}), ?_, ?_, ?_⟩
  · exact le_trans (Finset.card_image_le) (le_trans (Finset.card_filter_le _ _) hcard)
  · intro I hI
    obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp hI
    exact ((fib_cell ((hcells κ (Finset.mem_of_mem_filter κ hκ)).1) (psiV c)).preimage_mono
      strictMono_psi.monotone).isPreconnected
  · ext t
    simp only [Set.mem_ofPred_eq, Set.mem_sUnion]
    rw [hYeq, cons_mem_iff c t,
      mem_iff_exists_cell hcover hsep hZ'cube (psiV c) (psi t)]
    constructor
    · rintro ⟨κ, hκ, hκu⟩
      exact ⟨psi ⁻¹' {u : ℝ | Fin.snoc (psiV c) u ∈ κ},
        Finset.mem_image.mpr ⟨κ, hκ, rfl⟩, by simpa using hκu⟩
    · rintro ⟨I, hI, htI⟩
      obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp hI
      exact ⟨κ, hκ, by simpa using htI⟩

end Work.WilE10.UnifFinite

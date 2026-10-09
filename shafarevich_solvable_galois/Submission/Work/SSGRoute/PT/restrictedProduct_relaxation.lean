import Mathlib
import Submission.Work.SSGRoute.PT.pt_restrictedPairing
import Submission.Work.SSGRoute.PT.pt_localPairingDual
import Submission.Work.SSGRoute.PT.pt_piPairingDual
import Submission.Work.SSGRoute.PT.pt_isCompact_separation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The relaxation step of the Poitou–Tate workshop

Supporting material for `Work.SSGRoute.PT.restrictedProduct_relaxation`.
-/

namespace Work.SSGRoute.PT

open scoped RestrictedProduct

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {ι : Type*} {X Y : ι → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module (ZMod p) (X i)] [∀ i, Finite (X i)]
  [∀ i, TopologicalSpace (X i)] [∀ i, DiscreteTopology (X i)]
  [∀ i, AddCommGroup (Y i)] [∀ i, Module (ZMod p) (Y i)] [∀ i, Finite (Y i)]
  [∀ i, TopologicalSpace (Y i)] [∀ i, DiscreteTopology (Y i)]

/-- The evaluation `y ↦ y j` as a linear map on a restricted product. -/
def ptEvalLin (U' : ∀ i, Submodule (ZMod p) (Y i)) (j : ι) :
    (Πʳ i, [Y i, U' i]) →ₗ[ZMod p] Y j where
  toFun y := y j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma ptEvalLin_apply (U' : ∀ i, Submodule (ZMod p) (Y i)) (j : ι)
    (y : Πʳ i, [Y i, U' i]) : ptEvalLin U' j y = y j := rfl

/-- The element of `Πʳ i, [X i, U i]` whose value at `i` is `f i` for `i ∈ S` and `0` elsewhere
(the values of `f` outside `S` are irrelevant). -/
noncomputable def piSingle (U : ∀ i, Submodule (ZMod p) (X i)) [DecidableEq ι] (S : Finset ι)
    (f : ∀ i, X i) : Πʳ i, [X i, U i] :=
  ⟨fun j => if j ∈ S then f j else 0, by
    rw [Filter.eventually_cofinite]
    refine (S.finite_toSet).subset (fun j hj => ?_)
    by_contra hnot
    exact hj (by
      change (if j ∈ S then f j else 0) ∈ U j
      by_cases h : j ∈ S
      · exact absurd h hnot
      · rw [if_neg h]
        exact (U j).zero_mem)⟩

/-- The evaluation `x ↦ x j` as an additive homomorphism on the restricted product. -/
def ptEvalHomX (U : ∀ i, Submodule (ZMod p) (X i)) (j : ι) :
    (Πʳ i, [X i, U i]) →+ X j where
  toFun x := x j
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma ptEvalHomX_apply (U : ∀ i, Submodule (ZMod p) (X i)) (j : ι)
    (x : Πʳ i, [X i, U i]) : ptEvalHomX U j x = x j := rfl

lemma piSingle_apply_of_mem (U : ∀ i, Submodule (ZMod p) (X i)) [DecidableEq ι] {S : Finset ι}
    {f : ∀ i, X i} {j : ι} (hj : j ∈ S) :
    ((piSingle U S f : Πʳ i, [X i, U i]) : ∀ i, X i) j = f j := by
  rw [piSingle]
  simp [hj]

lemma piSingle_apply_of_notMem (U : ∀ i, Submodule (ZMod p) (X i)) [DecidableEq ι]
    {S : Finset ι} {f : ∀ i, X i} {j : ι} (hj : j ∉ S) :
    ((piSingle U S f : Πʳ i, [X i, U i]) : ∀ i, X i) j = 0 := by
  rw [piSingle]
  simp [hj]

lemma piSingle_apply_ite (U : ∀ i, Submodule (ZMod p) (X i)) [DecidableEq ι]
    {S : Finset ι} {f : ∀ i, X i} {j : ι} :
    ((piSingle U S f : Πʳ i, [X i, U i]) : ∀ i, X i) j = if j ∈ S then f j else 0 := by
  by_cases hj : j ∈ S
  · rw [piSingle_apply_of_mem U hj]; simp [hj]
  · rw [piSingle_apply_of_notMem U hj]; simp [hj]

lemma sub_piSingle_apply (U : ∀ i, Submodule (ZMod p) (X i)) [DecidableEq ι]
    (S : Finset ι) (f : ∀ i, X i) (v : Πʳ i, [X i, U i]) (j : ι) :
    ((v - piSingle U S f : Πʳ i, [X i, U i]) : ∀ i, X i) j
      = (v j : X j) - (if j ∈ S then f j else 0) := by
  have h := map_sub (ptEvalHomX U j) v (piSingle U S f)
  simp only [ptEvalHomX_apply] at h
  rw [h, piSingle_apply_ite]

/-- **The pairing of a `piSingle`-element** with any element of the dual restricted product is the
corresponding finite sum of local pairings. -/
theorem restrictedPairing_piSingle_left
    (U : ∀ i, Submodule (ZMod p) (X i)) (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (hβ0 : ∀ i, ∀ x ∈ U i, ∀ y ∈ U' i, β i x y = 0) [DecidableEq ι]
    (S : Finset ι) (f : ∀ i, X i) (y : Πʳ i, [Y i, U' i]) :
    restrictedPairing U U' β (piSingle U S f) y = ∑ i ∈ S, β i (f i) (y i) := by
  classical
  have hyfin : ({i | (y i : Y i) ∉ U' i}).Finite := Filter.eventually_cofinite.mp y.2
  set S' : Finset ι := S ∪ hyfin.toFinset with hS'def
  have hS : ∀ i ∉ S',
      ((piSingle U S f : Πʳ i, [X i, U i]) : ∀ i, X i) i ∈ U i ∧ (y i : Y i) ∈ U' i := by
    intro i hi
    have hiS : i ∉ S := fun h => hi (by rw [hS'def]; exact Finset.mem_union_left _ h)
    have hiY : i ∉ hyfin.toFinset := fun h => hi (by rw [hS'def]; exact Finset.mem_union_right _ h)
    refine ⟨?_, ?_⟩
    · rw [piSingle_apply_of_notMem U hiS]
      exact (U i).zero_mem
    · by_contra h
      exact hiY (hyfin.mem_toFinset.mpr h)
  rw [restrictedPairing_eq_sum U U' β hβ0 (piSingle U S f) y S' hS]
  rw [← Finset.sum_subset (Finset.subset_union_left) (fun i _ hiS => by
        rw [piSingle_apply_of_notMem U hiS]
        simp)]
  exact Finset.sum_congr rfl (fun i hi => by rw [piSingle_apply_of_mem U hi])

/-- Bridge between a sum over a `Finset` of an "extended" family of `X`-values and the sum over the
subtype indexing a finite product. -/
theorem sum_piSingle_bridge
    (_U : ∀ i, Submodule (ZMod p) (X i)) (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (F : Finset ι) (x' : (j : {j // j ∈ F}) → X (j : ι)) (xext : ∀ i, X i)
    (hxext : ∀ j (hj : j ∈ F), xext j = x' ⟨j, hj⟩) (b : Πʳ i, [Y i, U' i]) :
    (∑ j ∈ F, β j (xext j) (b j)) = ∑ j ∈ F.attach, β j.1 (x' j) (b j.1) := by
  rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hxext j j.2]

/-- A sum over the subtype `{j // j ∈ F}` is a sum over `F.attach`. -/
theorem sum_attach_eq_sum (F : Finset ι) (g : (j : {j // j ∈ F}) → ZMod p) :
    (∑ j : {j // j ∈ F}, g j) = ∑ j ∈ F.attach, g j := rfl

/-- **A compact subgroup of the dual restricted product is the double annihilator of its own
annihilator.**  If `B` is a compact subgroup of `Πʳ i, [Y i, U' i]` and `y ∉ B`, there is
`x ∈ Πʳ i, [X i, U i]` annihilating `B` but not `y`. -/
theorem pt_compact_annihilator_dual
    (U : ∀ i, Submodule (ZMod p) (X i)) (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (hβL : ∀ i, ∀ x : X i, (∀ y : Y i, β i x y = 0) → x = 0)
    (hβR : ∀ i, ∀ y : Y i, (∀ x : X i, β i x y = 0) → y = 0)
    (hβ0 : ∀ i, ∀ x ∈ U i, ∀ y ∈ U' i, β i x y = 0) [DecidableEq ι]
    (B : Submodule (ZMod p) (Πʳ i, [Y i, U' i]))
    (hB : IsCompact (B : Set (Πʳ i, [Y i, U' i])))
    {y : Πʳ i, [Y i, U' i]} (hy : y ∉ B) :
    ∃ x : Πʳ i, [X i, U i],
      (∀ b ∈ B, restrictedPairing U U' β x b = 0) ∧ restrictedPairing U U' β x y ≠ 0 := by
  classical
  obtain ⟨F, hF⟩ := pt_isCompact_separation (p := p) U' hB hy
  set ψ : (Πʳ i, [Y i, U' i]) →ₗ[ZMod p] ((j : {j // j ∈ F}) → Y (j : ι)) :=
    LinearMap.pi (fun j : {j // j ∈ F} => ptEvalLin U' (j : ι)) with hψdef
  set D : Submodule (ZMod p) ((j : {j // j ∈ F}) → Y (j : ι)) := B.map ψ with hDdef
  set q : (j : {j // j ∈ F}) → Y (j : ι) := fun j => y (j : ι) with hqdef
  have hqD : q ∉ D := by
    rw [hDdef, Submodule.mem_map]
    rintro ⟨b, hb, hbq⟩
    obtain ⟨j, hjF, hjne⟩ := hF b hb
    have h1 : ψ b (⟨j, hjF⟩ : {j // j ∈ F}) = q ⟨j, hjF⟩ := by rw [hbq]
    rw [hψdef, hqdef] at h1
    simp only [LinearMap.pi_apply, ptEvalLin_apply] at h1
    exact hjne h1
  obtain ⟨x', hxD, hxq⟩ := pt_piPairingDual (p := p) (F := {j // j ∈ F})
    (X := fun j => X (j : ι)) (Y := fun j => Y (j : ι)) (β := fun j => β (j : ι))
    (fun j => hβL (j : ι)) (fun j => hβR (j : ι)) D q hqD
  set xext : ∀ i, X i := fun j => if h : j ∈ F then x' ⟨j, h⟩ else 0 with hxextdef
  have hxext : ∀ j (hj : j ∈ F), xext j = x' ⟨j, hj⟩ := by
    intro j hj; rw [hxextdef]; exact dif_pos hj
  refine ⟨piSingle U F xext, ?_, ?_⟩
  · intro b hb
    rw [restrictedPairing_piSingle_left U U' β hβ0 F xext b]
    rw [sum_piSingle_bridge U U' β F x' xext hxext b]
    have hbD : ψ b ∈ D := Submodule.mem_map_of_mem hb
    have hzero := hxD (ψ b) hbD
    rw [hψdef] at hzero
    simp only [LinearMap.pi_apply, ptEvalLin_apply] at hzero
    rw [sum_attach_eq_sum F (fun j => β j.1 (x' j) (b j.1))] at hzero
    exact hzero
  · rw [restrictedPairing_piSingle_left U U' β hβ0 F xext y]
    rw [sum_piSingle_bridge U U' β F x' xext hxext y]
    rw [hqdef] at hxq
    rw [sum_attach_eq_sum F (fun j => β j.1 (x' j) (q j))] at hxq
    exact hxq


/-- The "single coordinate" embedding `x ↦ single i x` as a linear map. -/
def singleLin (U : ∀ i, Submodule (ZMod p) (X i)) [DecidableEq ι] (i : ι) :
    X i →ₗ[ZMod p] (Πʳ i, [X i, U i]) where
  toFun x := RestrictedProduct.single U i x
  map_add' x y := RestrictedProduct.single_add U i x y
  map_smul' c x := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [RestrictedProduct.smul_apply, RestrictedProduct.single_eq_of_ne U (c • x) hj,
        RestrictedProduct.single_eq_of_ne U x hj, smul_zero]

@[simp] lemma singleLin_apply (U : ∀ i, Submodule (ZMod p) (X i)) [DecidableEq ι] (i : ι)
    (x : X i) : singleLin U i x = RestrictedProduct.single U i x := rfl

/-- **Realisation of the functionals that vanish on the relaxation subgroup.**  If
`W = {w ∈ Πʳ [X i, U i] : w_i = 0 for i ∈ T, w_i ∈ U i for i ∉ Ram}` (`T ⊆ Ram`, `T` finite), then
every `𝔽_p`-linear functional `L` on the restricted product that vanishes on `W` is given by pairing
with an element `b` of the dual restricted product satisfying `b_i ∈ U' i` for `i ∉ Ram` and
`b_i = 0` for `i ∈ Ram ∖ T`. -/
theorem pt_fun_vanishing_relaxation
    (U : ∀ i, Submodule (ZMod p) (X i)) (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (hβL : ∀ i, ∀ x : X i, (∀ y : Y i, β i x y = 0) → x = 0)
    (hβR : ∀ i, ∀ y : Y i, (∀ x : X i, β i x y = 0) → y = 0)
    (hβ0 : ∀ i, ∀ x ∈ U i, ∀ y ∈ U' i, β i x y = 0)
    (hU : ∀ i, ∀ y : Y i, y ∈ U' i ↔ ∀ x : X i, x ∈ U i → β i x y = 0)
    (T : Finset ι) (Ram : Set ι) (hTRam : ∀ i ∈ T, i ∈ Ram) [DecidableEq ι]
    (L : (Πʳ i, [X i, U i]) →ₗ[ZMod p] ZMod p)
    (hL : ∀ w : Πʳ i, [X i, U i],
      (∀ i ∈ T, (w i : X i) = 0) → (∀ i, i ∉ Ram → (w i : X i) ∈ U i) → L w = 0) :
    ∃ b : Πʳ i, [Y i, U' i],
      (∀ i, i ∉ Ram → (b i : Y i) ∈ U' i) ∧
      (∀ i, i ∈ Ram → i ∉ T → (b i : Y i) = 0) ∧
      ∀ v : Πʳ i, [X i, U i], L v = restrictedPairing U U' β v b := by
  classical
  -- (1) `L` vanishes on the `single` elements contained in the relaxation subgroup
  have hWT : ∀ (i : ι) (x : X i), i ∈ Ram → i ∉ T →
      L (RestrictedProduct.single U i x) = 0 := by
    intro i x hRam hT
    apply hL
    · intro j hj
      by_cases hji : j = i
      · exfalso
        rw [hji] at hj
        exact hT hj
      · rw [RestrictedProduct.single_eq_of_ne U x hji]
    · intro j hjRam
      by_cases hji : j = i
      · exfalso
        rw [hji] at hjRam
        exact hjRam hRam
      · rw [RestrictedProduct.single_eq_of_ne U x hji]
        exact (U j).zero_mem
  have hWU : ∀ (i : ι) (u : X i), u ∈ U i → i ∉ Ram →
      L (RestrictedProduct.single U i u) = 0 := by
    intro i u hu hRam
    apply hL
    · intro j hj
      by_cases hji : j = i
      · exfalso
        rw [hji] at hj
        exact hRam (hTRam i hj)
      · rw [RestrictedProduct.single_eq_of_ne U u hji]
    · intro j hjRam
      by_cases hji : j = i
      · rw [hji, RestrictedProduct.single_eq_same]
        exact hu
      · rw [RestrictedProduct.single_eq_of_ne U u hji]
        exact (U j).zero_mem
  -- (2) the local values of `b`
  have hlocal : ∀ i, ∃ y : Y i,
      (i ∈ T → ∀ x : X i, L (RestrictedProduct.single U i x) = β i x y) ∧
      (i ∈ Ram → i ∉ T → y = 0) ∧
      (i ∉ Ram → y ∈ U' i ∧ ∀ x : X i, L (RestrictedProduct.single U i x) = β i x y) := by
    intro i
    by_cases hiT : i ∈ T
    · obtain ⟨y, hy⟩ := (pt_localPairingDual (p := p) (X := X i) (Y := Y i) (β := β i)
        (hβL i) (hβR i) (U i) (U' i) (hU i)).1 (L.comp (singleLin U i))
      exact ⟨y, fun _ => hy, fun _ h2 => absurd hiT h2, fun h1 => absurd (hTRam i hiT) h1⟩
    · by_cases hiR : i ∈ Ram
      · exact ⟨0, fun h => absurd h hiT, fun _ _ => rfl, fun h => absurd hiR h⟩
      · obtain ⟨y, hy⟩ := (pt_localPairingDual (p := p) (X := X i) (Y := Y i) (β := β i)
          (hβL i) (hβR i) (U i) (U' i) (hU i)).1 (L.comp (singleLin U i))
        refine ⟨y, fun h => absurd h hiT, fun h1 _ => absurd h1 hiR, fun _ => ⟨?_, hy⟩⟩
        rw [hU i y]
        intro x hx
        rw [← hy x]
        exact hWU i x hx hiR
  choose b hbT hbRT hbR using hlocal
  have hbout : ∀ i, i ∉ T → (b i : Y i) ∈ U' i := by
    intro i hiT
    by_cases hiR : i ∈ Ram
    · rw [hbRT i hiR hiT]
      exact (U' i).zero_mem
    · exact (hbR i hiR).1
  have hbRam : ∀ i, i ∈ Ram → i ∉ T → (b i : Y i) = 0 := fun i h1 h2 => hbRT i h1 h2
  have hbPi : ∀ᶠ i in Filter.cofinite, (b i : Y i) ∈ U' i := by
    rw [Filter.eventually_cofinite]
    refine (T.finite_toSet).subset (fun i hi => ?_)
    by_contra hiT
    exact hi (hbout i hiT)
  have hbU' : ∀ i, i ∉ Ram → (b i : Y i) ∈ U' i := by
    intro i hiR
    by_cases hiT : i ∈ T
    · exact absurd (hTRam i hiT) hiR
    · exact hbout i hiT
  refine ⟨⟨b, hbPi⟩, hbU', hbRam, ?_⟩
  intro v
  have hvfin : ({i | (v i : X i) ∉ U i}).Finite := Filter.eventually_cofinite.mp v.2
  set E : Finset ι := hvfin.toFinset with hEdef
  set S : Finset ι := T ∪ E with hSdef
  -- the decomposition of `L (piSingle …)` into the single contributions
  have hsumL : ∀ S' : Finset ι, L (piSingle U S' (fun i => v i))
      = ∑ i ∈ S', L (RestrictedProduct.single U i (v i)) := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      have h0 : piSingle U (∅ : Finset ι) (fun i => v i) = 0 := by
        ext j
        rw [piSingle_apply_ite]
        simp
      rw [h0, map_zero, Finset.sum_empty]
    | insert a S' ha ih =>
      have hstep : piSingle U (insert a S') (fun i => v i)
          = RestrictedProduct.single U a (v a) + piSingle U S' (fun i => v i) := by
        ext j
        rw [RestrictedProduct.add_apply, piSingle_apply_ite, piSingle_apply_ite]
        by_cases hja : j = a
        · rw [hja]
          rw [if_pos (Finset.mem_insert_self a S'), RestrictedProduct.single_eq_same,
            if_neg (fun hcon => ha hcon), add_zero]
        · rw [RestrictedProduct.single_eq_of_ne U (v a) hja]
          by_cases hjS : j ∈ S'
          · rw [if_pos (Finset.mem_insert.mpr (Or.inr hjS)), if_pos hjS, zero_add]
          · rw [if_neg (fun hcon => (Finset.mem_insert.mp hcon).elim hja hjS), if_neg hjS,
              add_zero]
      rw [hstep, map_add, ih, Finset.sum_insert ha]
  -- the leftover term lies in the relaxation subgroup
  have hleft : L (v - piSingle U S (fun i => v i)) = 0 := by
    apply hL
    · intro j hj
      rw [sub_piSingle_apply U S (fun i => v i) v j,
        if_pos (by rw [hSdef]; exact Finset.mem_union_left _ hj), sub_self]
    · intro j hjRam
      rw [sub_piSingle_apply U S (fun i => v i) v j]
      by_cases hjS : j ∈ S
      · rw [if_pos hjS, sub_self]
        exact (U j).zero_mem
      · rw [if_neg hjS, sub_zero]
        by_contra hcon
        exact hjS (by rw [hSdef]; exact Finset.mem_union_right _ (hvfin.mem_toFinset.mpr hcon))
  have hLv : L v = L (piSingle U S (fun i => v i)) := by
    have h2 : piSingle U S (fun i => v i) + (v - piSingle U S (fun i => v i)) = v := by abel
    have h3 : L (piSingle U S (fun i => v i) + (v - piSingle U S (fun i => v i))) = L v := by
      rw [h2]
    rw [map_add, hleft, add_zero] at h3
    exact h3.symm
  -- the pairing side
  have hpair : restrictedPairing U U' β v ⟨b, hbPi⟩ = ∑ i ∈ S, β i (v i) (b i) := by
    refine restrictedPairing_eq_sum U U' β hβ0 v ⟨b, hbPi⟩ S (fun i hi => ⟨?_, ?_⟩)
    · by_contra hcon
      exact hi (by rw [hSdef]; exact Finset.mem_union_right _ (hvfin.mem_toFinset.mpr hcon))
    · by_contra hcon
      have hiT : i ∈ T := by
        by_contra hiT
        exact hcon (hbout i hiT)
      exact hi (by rw [hSdef]; exact Finset.mem_union_left _ hiT)
  have hterm : ∀ i ∈ S, L (RestrictedProduct.single U i (v i)) = β i (v i) (b i) := by
    intro i hiS
    by_cases hiT : i ∈ T
    · exact hbT i hiT (v i)
    · by_cases hiR : i ∈ Ram
      · rw [hbRT i hiR hiT, hWT i (v i) hiR hiT]
        simp
      · exact (hbR i hiR).2 (v i)
  rw [hpair, hLv, hsumL S]
  exact Finset.sum_congr rfl (fun i hi => hterm i hi)

/-- **The relaxation step of `DESIGN_PT.md` §3** (see the module docstring of
`Submission/Work/SSGRoute/PT/pt_restrictedPairing.lean` for the pairing `restrictedPairing` and its
computation rule `restrictedPairing_eq_sum`).

Setting: an index type `ι` (the places together with the involutions), finite 𝔽_p-vector spaces
`X i, Y i` (with the discrete topology) paired by pairings `β i` (additive in each variable,
non-degenerate in both), subgroups `U i ≤ X i` with `U' i = (U i)^⊥`, the restricted products
`Πʳ i, [X i, U i]`, `Πʳ i, [Y i, U' i]` (so that the total pairing is a finite sum, hypothesis
`hβ0` saying that the "unramified" subgroups annihilate each other), a set `Ram` of places where
ramification is allowed, a finite set `T ⊆ Ram` of places where data are prescribed, and subgroups
`A ≤ Πʳ [X i, U i]`, `B ≤ Πʳ [Y i, U' i]` which are the images of the global classes of the
*unrestricted* Poitou–Tate middle exactness (`hAB` is the exactness `A = B^⊥`).

Conclusion: every `x` on `T` orthogonal to the *Selmer* part of `B` (the classes unramified off
`Ram` and trivial on `Ram ∖ T`) is the `T`-part of a class of `A` that is unramified off `Ram`.
This is exactly what the counting argument of `Work.SSGRoute.pt_selmer_relaxed` needs. -/
theorem restrictedProduct_relaxation
    (p : ℕ) [Fact p.Prime]
    {ι : Type*} {X Y : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module (ZMod p) (X i)] [∀ i, Finite (X i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, DiscreteTopology (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module (ZMod p) (Y i)] [∀ i, Finite (Y i)]
    [∀ i, TopologicalSpace (Y i)] [∀ i, DiscreteTopology (Y i)]
    (U : ∀ i, Submodule (ZMod p) (X i)) (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (hβL : ∀ i, ∀ x : X i, (∀ y : Y i, β i x y = 0) → x = 0)
    (hβR : ∀ i, ∀ y : Y i, (∀ x : X i, β i x y = 0) → y = 0)
    (hβ0 : ∀ i, ∀ x ∈ U i, ∀ y ∈ U' i, β i x y = 0)
    (hU : ∀ i, ∀ y : Y i, y ∈ U' i ↔ ∀ x : X i, x ∈ U i → β i x y = 0)
    (Ram : Set ι) (T : Finset ι) (hTRam : ∀ i ∈ T, i ∈ Ram)
    (A : Submodule (ZMod p) (Πʳ i, [X i, U i]))
    (B : Submodule (ZMod p) (Πʳ i, [Y i, U' i]))
    (hAcomp : IsCompact (A : Set (Πʳ i, [X i, U i])))
    (hBcomp : IsCompact (B : Set (Πʳ i, [Y i, U' i])))
    (hAB : ∀ a : Πʳ i, [X i, U i],
      a ∈ A ↔ ∀ b : Πʳ i, [Y i, U' i], b ∈ B → restrictedPairing U U' β a b = 0)
    (x : (i : T) → X i)
    (hx : ∀ b : Πʳ i, [Y i, U' i], b ∈ B →
      (∀ i, i ∉ Ram → (b i : Y i) ∈ U' i) → (∀ i, i ∈ Ram → i ∉ T → (b i : Y i) = 0) →
      ∑ i : T, β i (x i) (b (i : ι)) = 0) :
    ∃ a : Πʳ i, [X i, U i], a ∈ A ∧ (∀ i, i ∉ Ram → (a i : X i) ∈ U i) ∧
      (∀ i : T, a (i : ι) = x i) := by
  classical
  -- the relaxation subgroup
  let W : Submodule (ZMod p) (Πʳ i, [X i, U i]) :=
    { carrier := {w | (∀ i ∈ T, (w i : X i) = 0) ∧ (∀ i, i ∉ Ram → (w i : X i) ∈ U i)}
      zero_mem' := by
        constructor
        · intro i _; rfl
        · intro i _; exact (U i).zero_mem
      add_mem' := by
        intro a b ha hb
        constructor
        · intro i hi
          change (a i : X i) + b i = 0
          rw [ha.1 i hi, hb.1 i hi, add_zero]
        · intro i hi
          change (a i : X i) + b i ∈ U i
          exact (U i).add_mem (ha.2 i hi) (hb.2 i hi)
      smul_mem' := by
        intro c a ha
        constructor
        · intro i hi
          change c • (a i : X i) = 0
          rw [ha.1 i hi, smul_zero]
        · intro i hi
          change c • (a i : X i) ∈ U i
          exact (U i).smul_mem c (ha.2 i hi) }
  -- the test element `z`
  set fz : ∀ i, X i := fun i => if h : i ∈ T then x ⟨i, h⟩ else 0 with hfzdef
  set z : Πʳ i, [X i, U i] := piSingle U T fz with hzdef
  have hfz : ∀ j (hj : j ∈ T), fz j = x ⟨j, hj⟩ := by
    intro j hj
    rw [hfzdef]
    simp only [dif_pos hj]
  have hzT : ∀ j (hj : j ∈ T), ((z : Πʳ i, [X i, U i]) : ∀ i, X i) j = x ⟨j, hj⟩ := by
    intro j hj
    rw [hzdef, piSingle_apply_of_mem U hj]
    exact hfz j hj
  have hzN : ∀ j, j ∉ T → ((z : Πʳ i, [X i, U i]) : ∀ i, X i) j = 0 := by
    intro j hj
    rw [hzdef, piSingle_apply_of_notMem U hj]
  -- the pairing of `z` against any element of the dual restricted product
  have hzsum : ∀ b : Πʳ i, [Y i, U' i],
      restrictedPairing U U' β z b = ∑ i : T, β i (x i) (b (i : ι)) := by
    intro b
    rw [hzdef, restrictedPairing_piSingle_left U U' β hβ0 T fz b]
    rw [sum_piSingle_bridge U U' β T x fz hfz b]
    rw [← sum_attach_eq_sum T (fun j => β j.1 (x j) (b j.1))]
  -- the annihilator of `A` is `B`
  have hAann : ∀ y : Πʳ i, [Y i, U' i],
      (∀ a ∈ A, restrictedPairing U U' β a y = 0) → y ∈ B := by
    intro y hy
    by_contra hyB
    obtain ⟨a, ha, hay⟩ := pt_compact_annihilator_dual U U' β hβL hβR hβ0 B hBcomp hyB
    exact hay (hy a ((hAB a).mpr ha))
  -- the main step: `z` lies in `A + W`
  have hz : z ∈ A ⊔ W := by
    by_contra hzin
    have hcl : W.mkQ z ∉ A.map W.mkQ := by
      rw [Submodule.mem_map]
      rintro ⟨a, ha, haz⟩
      apply hzin
      refine Submodule.mem_sup.mpr ⟨a, ha, z - a, ?_, ?_⟩
      · have h1 : a - z ∈ W := by
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at haz
          exact (Submodule.Quotient.eq W).mp haz
        simpa using W.neg_mem h1
      · abel
    obtain ⟨g, hgker, hgz⟩ := LinearMap.exists_extend_of_notMem (p := A.map W.mkQ)
      (0 : ↥(A.map W.mkQ) →ₗ[ZMod p] ZMod p) hcl 1
    set L : (Πʳ i, [X i, U i]) →ₗ[ZMod p] ZMod p := g.comp W.mkQ with hLdef
    have hker : ∀ a ∈ A, L a = 0 := by
      intro a ha
      have h2 := LinearMap.congr_fun hgker
        (⟨W.mkQ a, Submodule.mem_map_of_mem ha⟩ : ↥(A.map W.mkQ))
      simpa [hLdef] using h2
    have hLW : ∀ w : Πʳ i, [X i, U i],
        (∀ i ∈ T, (w i : X i) = 0) → (∀ i, i ∉ Ram → (w i : X i) ∈ U i) → L w = 0 := by
      intro w h1 h2
      have hw : w ∈ W := ⟨h1, h2⟩
      have h0 : W.mkQ w = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hw
      rw [hLdef, LinearMap.comp_apply, h0, map_zero]
    obtain ⟨b, hbU, hbR0, hbL⟩ :=
      pt_fun_vanishing_relaxation U U' β hβL hβR hβ0 hU T Ram hTRam L hLW
    have hbB : b ∈ B := by
      apply hAann
      intro a ha
      rw [← hbL a]
      exact hker a ha
    have h1 : (∑ i : T, β i (x i) (b (i : ι))) = 0 := hx b hbB hbU hbR0
    have h3 : restrictedPairing U U' β z b = 1 := by
      rw [← hbL z, hLdef, LinearMap.comp_apply, hgz]
    have h4 : restrictedPairing U U' β z b = 0 := by rw [hzsum b, h1]
    rw [h4] at h3
    exact absurd h3 (by simp)
  -- conclusion
  obtain ⟨a, ha, w, hw, haw⟩ := Submodule.mem_sup.mp hz
  refine ⟨a, ha, ?_, ?_⟩
  · intro i hiRam
    have hiT : i ∉ T := fun h => hiRam (hTRam i h)
    have h1 : ((z : Πʳ i, [X i, U i]) : ∀ i, X i) i = 0 := hzN i hiT
    have h2 : (w i : X i) ∈ U i := hw.2 i hiRam
    have h3 : (a i : X i) + w i = (z i : X i) := by
      have hh := congrArg (fun t : Πʳ i, [X i, U i] => (t : ∀ i, X i) i) haw
      simpa using hh
    rw [h1] at h3
    have h4 : (a i : X i) = -w i := (add_eq_zero_iff_eq_neg.mp h3)
    rw [h4]
    exact (U i).neg_mem h2
  · intro i
    have h1 : ((z : Πʳ i, [X i, U i]) : ∀ i, X i) (i : ι) = x i := hzT (i : ι) i.2
    have h2 : (w (i : ι) : X i) = 0 := hw.1 (i : ι) i.2
    have h3 : (a (i : ι) : X i) + w (i : ι) = (z (i : ι) : X i) := by
      have hh := congrArg (fun t : Πʳ i, [X i, U i] => (t : ∀ i, X i) (i : ι)) haw
      simpa using hh
    rw [h2, add_zero] at h3
    rw [h3, h1]

end Work.SSGRoute.PT

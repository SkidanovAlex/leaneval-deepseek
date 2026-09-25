import Mathlib
import Submission.Work.LT.good_base_defs

/-!
# Extension operators and the Kalachev--Panteleev `extend` map

Infrastructure for `Work.LT.gb_extension` (Kalachev--Panteleev, *Two-sided robustly testable
codes*, arXiv 2206.09973, Lemma "extend-cwpart").

All matrices are `Fin D × Fin D → ZMod 2`, rows indexed by the first coordinate.

* `GB.projA A` is the coordinate projection onto the coordinates in `A`.
* `GB.ExtOp C A` is an `A`-extension operator for a code `C`: a linear endomorphism `T` of `𝔽₂^D`
  which fixes the coordinates in `A` (`T v k = v k` for `k ∈ A`), vanishes on vectors supported
  outside `A` (`T v = T (projA A v)`), and preserves `C` (`T c ∈ C` for `c ∈ C`).
  Such `T` exists for every `C` and `A` (see `GB.extOp_nonempty`), and is the formalization of the
  operator `g_i` of the paper.
* `GB.matExt A B u w x` is the matrix with entries `∑ i ∈ A, ∑ j ∈ B, x (i,j) * u i k * w j l`;
  it is `(g₁ ⊗ g₂) x(A,B)` in the notation of the paper, i.e. `U x Wᵀ` for `u i` the columns of `U`
  and `w j` the columns of `W`.
-/

namespace Work.LT

namespace GB

variable {D : ℕ}

/-- The coordinate projection onto the coordinates indexed by `A`. -/
noncomputable def projA (A : Finset (Fin D)) : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) where
  toFun v := fun k => if k ∈ A then v k else 0
  map_add' u v := by
    funext k; by_cases hk : k ∈ A <;> simp [hk]
  map_smul' c v := by
    funext k; by_cases hk : k ∈ A <;> simp [hk]

lemma projA_apply (A : Finset (Fin D)) (v : Fin D → ZMod 2) (k : Fin D) :
    projA A v k = if k ∈ A then v k else 0 := rfl

lemma projA_idem (A : Finset (Fin D)) (v : Fin D → ZMod 2) :
    projA A (projA A v) = projA A v := by
  funext k
  rw [projA_apply, projA_apply]
  by_cases hk : k ∈ A <;> simp [hk]

lemma projA_single_mem (A : Finset (Fin D)) {i : Fin D} (hi : i ∈ A) :
    projA A (Pi.single i (1 : ZMod 2)) = Pi.single i (1 : ZMod 2) := by
  funext k
  rw [projA_apply]
  by_cases hk : k ∈ A
  · simp [hk]
  · have hki : k ≠ i := fun h => hk (h ▸ hi)
    rw [if_neg hk, Pi.single_eq_of_ne hki]

lemma projA_single_notMem (A : Finset (Fin D)) {i : Fin D} (hi : i ∉ A) :
    projA A (Pi.single i (1 : ZMod 2)) = 0 := by
  funext k
  rw [projA_apply]
  by_cases hk : k ∈ A
  · have hki : k ≠ i := fun h => hi (h ▸ hk)
    rw [if_pos hk, Pi.single_eq_of_ne hki, Pi.zero_apply]
  · rw [if_neg hk, Pi.zero_apply]

/-- A vector is the sum of its coordinates times the standard basis vectors. -/
lemma sum_single_univ (v : Fin D → ZMod 2) :
    v = ∑ i ∈ (Finset.univ : Finset (Fin D)), v i • Pi.single i (1 : ZMod 2) := by
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

lemma projA_eq_sum (A : Finset (Fin D)) (v : Fin D → ZMod 2) :
    projA A v = ∑ i ∈ A, v i • Pi.single i (1 : ZMod 2) := by
  funext k
  rw [projA_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- An `A`-extension operator for a code `C`. -/
structure ExtOp (C : Submodule (ZMod 2) (Fin D → ZMod 2)) (A : Finset (Fin D)) where
  /-- the underlying linear map -/
  toLin : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)
  /-- it fixes the coordinates in `A` -/
  agree : ∀ (v : Fin D → ZMod 2) (k : Fin D), k ∈ A → toLin v k = v k
  /-- it vanishes on vectors vanishing on `A` -/
  vanish : ∀ v : Fin D → ZMod 2, toLin v = toLin (projA A v)
  /-- it preserves `C` -/
  preserves : ∀ c ∈ C, toLin c ∈ C

variable {C : Submodule (ZMod 2) (Fin D → ZMod 2)} {A : Finset (Fin D)}

/-- The image of the `i`-th standard basis vector under an extension operator. -/
noncomputable def opVec (T : ExtOp C A) (i : Fin D) : Fin D → ZMod 2 :=
  T.toLin (Pi.single i (1 : ZMod 2))

lemma opVec_apply (T : ExtOp C A) (i : Fin D) :
    opVec T i = T.toLin (Pi.single i (1 : ZMod 2)) := rfl

/-- A vector vanishing on `A` is killed by an extension operator. -/
lemma ExtOp.toLin_eq_zero_of_vanishing (T : ExtOp C A) {v : Fin D → ZMod 2}
    (hv : ∀ k, k ∈ A → v k = 0) : T.toLin v = 0 := by
  have h : projA A v = 0 := by
    funext k
    rw [projA_apply]
    by_cases hk : k ∈ A
    · rw [if_pos hk, hv k hk, Pi.zero_apply]
    · rw [if_neg hk, Pi.zero_apply]
  rw [T.vanish v, h, map_zero]

lemma ExtOp.opVec_eq_zero (T : ExtOp C A) {i : Fin D} (hi : i ∉ A) : opVec T i = 0 :=
  T.toLin_eq_zero_of_vanishing (fun k hk => by
    rw [Pi.single_eq_of_ne (show k ≠ i by rintro rfl; exact hi hk)])

lemma ExtOp.opVec_agree (T : ExtOp C A) {i k : Fin D} (hk : k ∈ A) :
    opVec T i k = if k = i then 1 else 0 := by
  by_cases hi : i ∈ A
  · rw [opVec_apply, T.agree _ _ hk, Pi.single_apply]
  · rw [T.opVec_eq_zero hi]
    by_cases hki : k = i
    · exact absurd (hki ▸ hk) hi
    · simp [hki]

/-- The matrix `(g₁ ⊗ g₂) y(A,B)`: rows indexed by `A` and columns by `B` are replaced by the
vectors `u i`, `w j`. -/
noncomputable def matExt (A B : Finset (Fin D)) (u w : Fin D → (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) : Fin D × Fin D → ZMod 2 :=
  fun p => ∑ i ∈ A, ∑ j ∈ B, x (i, j) * u i p.1 * w j p.2

lemma matExt_apply (A B : Finset (Fin D)) (u w : Fin D → (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) (p : Fin D × Fin D) :
    matExt A B u w x p = ∑ i ∈ A, ∑ j ∈ B, x (i, j) * u i p.1 * w j p.2 := rfl

lemma matExt_add (A B : Finset (Fin D)) (u w : Fin D → (Fin D → ZMod 2))
    (x y : Fin D × Fin D → ZMod 2) :
    matExt A B u w (x + y) = matExt A B u w x + matExt A B u w y := by
  funext p
  simp only [matExt, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Extension operators exist.**  For every subspace `C ⊆ 𝔽₂^D` and every `A ⊆ [D]`
there is an `A`-extension operator: the formalization of the operators `g_i` of
Kalachev--Panteleev's "extend" lemma.

Split `V = ker π ⊔ (K_C ⊔ W')` where `π` is the projection onto the coordinates in `A`, `K_C` is a
complement of `C ⊓ ker π` inside `C` and `W'` is a complement of `C + ker π`; then `π` restricts to
an isomorphism `K_C ⊔ W' ≅ π(V)`, whose inverse `σ` is the required section: `π ∘ σ = id` and
`σ(π c) ∈ (K_C ⊔ W') ⊓ (C + ker π) = K_C ⊆ C`. -/
theorem extOp_nonempty {D : ℕ} (C : Submodule (ZMod 2) (Fin D → ZMod 2))
    (A : Finset (Fin D)) : Nonempty (ExtOp C A) := by
  classical
  set π : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) := projA A with hπ
  set K0 : Submodule (ZMod 2) (Fin D → ZMod 2) := LinearMap.ker π with hK0
  -- `K_C`: a complement of `C ⊓ ker π` inside `C`
  obtain ⟨L, hL⟩ := Submodule.exists_isCompl (C ⊓ K0)
  set KC : Submodule (ZMod 2) (Fin D → ZMod 2) := L ⊓ C with hKC
  -- `W'`: a complement of `C + ker π`
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (C ⊔ K0)
  set KK : Submodule (ZMod 2) (Fin D → ZMod 2) := KC ⊔ W' with hKK
  have hle_C : C ≤ C ⊔ K0 := le_sup_left
  have hle_K0 : K0 ≤ C ⊔ K0 := le_sup_right
  have hKC_le_C : KC ≤ C := by rw [hKC]; exact inf_le_right
  have hKC_le_L : KC ≤ L := by rw [hKC]; exact inf_le_left
  have hKC_disj : KC ⊓ K0 = ⊥ := by
    rw [hKC]
    apply le_bot_iff.mp
    intro x hx
    rw [Submodule.mem_inf] at hx
    have hx' : x ∈ (C ⊓ K0) ⊓ L := ⟨⟨hx.1.2, hx.2⟩, hx.1.1⟩
    rw [hL.inf_eq_bot] at hx'
    simpa using hx'
  -- `C = (C ⊓ ker π) ⊔ K_C`
  have hC_decomp : C ⊓ K0 ⊔ KC = C := by
    refine le_antisymm (sup_le inf_le_left hKC_le_C) ?_
    intro c hc
    have hc' : c ∈ (C ⊓ K0) ⊔ L := by rw [hL.sup_eq_top]; trivial
    obtain ⟨w, hw, l, hl, hwl⟩ := Submodule.mem_sup.mp hc'
    refine Submodule.mem_sup.mpr ⟨w, hw, l, ⟨hl, ?_⟩, hwl⟩
    have hl' : l = c - w := by rw [← hwl]; abel
    exact hl' ▸ Submodule.sub_mem C hc hw.1
  -- `K0 ⊓ (K_C ⊔ W') = ⊥`
  have hKK_disj : K0 ⊓ KK = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨hx0, hxK⟩ := Submodule.mem_inf.mp hx
    have hxK' : x ∈ KC ⊔ W' := hKK ▸ hxK
    obtain ⟨k, hk, w, hw, hkw⟩ := Submodule.mem_sup.mp hxK'
    have hwU : w ∈ C ⊔ K0 := by
      have hwk : w = x - k := by rw [← hkw]; abel
      rw [hwk]
      exact Submodule.sub_mem _ (hle_K0 hx0) (hle_C (hKC_le_C hk))
    have hwbot : w ∈ (C ⊔ K0) ⊓ W' := ⟨hwU, hw⟩
    rw [hW'.inf_eq_bot] at hwbot
    have hw0 : w = 0 := by simpa using hwbot
    have hx_eq : x = k := by rw [← hkw, hw0, add_zero]
    rw [hx_eq]
    have hkK0 : k ∈ K0 := by rw [← hx_eq]; exact hx0
    have hkk : k ∈ KC ⊓ K0 := ⟨hk, hkK0⟩
    rw [hKC_disj] at hkk
    simpa using hkk
  -- `K0 ⊔ (K_C ⊔ W') = ⊤`
  have hKK_sup : K0 ⊔ KK = ⊤ := by
    apply top_le_iff.mp
    rw [← hW'.sup_eq_top]
    refine sup_le (sup_le ?_ le_sup_left) ?_
    · rw [← hC_decomp]
      refine sup_le ?_ ?_
      · calc C ⊓ K0 ≤ K0 := inf_le_right
          _ ≤ K0 ⊔ KK := le_sup_left
      · calc KC ≤ KK := le_sup_left
          _ ≤ K0 ⊔ KK := le_sup_right
    · calc W' ≤ KC ⊔ W' := le_sup_right
        _ = KK := hKK.symm
        _ ≤ K0 ⊔ KK := le_sup_right
  have hmapK0 : Submodule.map π K0 = ⊥ := by
    apply le_bot_iff.mp
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    have hx0 : π x = 0 := LinearMap.mem_ker.mp (hK0 ▸ hx)
    simpa using hx0
  have hker_bot : (π.comp KK.subtype).ker = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hx0 : π ((KK.subtype x : Fin D → ZMod 2)) = 0 := LinearMap.mem_ker.mp hx
    have hxK0 : ((KK.subtype x : Fin D → ZMod 2)) ∈ K0 := by
      rw [hK0]
      exact LinearMap.mem_ker.mpr hx0
    have hboth : (KK.subtype x : Fin D → ZMod 2) ∈ K0 ⊓ KK := ⟨hxK0, x.2⟩
    rw [hKK_disj] at hboth
    exact Subtype.ext (by simpa [Submodule.subtype_apply] using hboth)
  have hinj : Function.Injective (π.comp KK.subtype) := LinearMap.ker_eq_bot.mp hker_bot
  have hrange : (π.comp KK.subtype).range = Submodule.map π ⊤ := by
    have h1 : (π.comp KK.subtype).range = Submodule.map π KK := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have h2 : Submodule.map π ⊤ = Submodule.map π KK := by
      conv_lhs => rw [← hKK_sup, Submodule.map_sup, hmapK0, bot_sup_eq]
    rw [h1, h2]
  let e : ↥KK ≃ₗ[ZMod 2] ↥(Submodule.map π ⊤) :=
    (LinearEquiv.ofInjective (π.comp KK.subtype) hinj).trans
      (LinearEquiv.ofEq (π.comp KK.subtype).range (Submodule.map π ⊤) hrange)
  have he_val : ∀ y : ↥KK,
      (((e y : ↥(Submodule.map π ⊤)) : Fin D → ZMod 2)) = π (y : Fin D → ZMod 2) := by
    intro y
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.ofInjective_apply]
    exact LinearEquiv.coe_ofEq_apply hrange _
  let σ : ↥(Submodule.map π ⊤) →ₗ[ZMod 2] (Fin D → ZMod 2) := KK.subtype.comp e.symm.toLinearMap
  have hσ_val : ∀ u : ↥(Submodule.map π ⊤), σ u = ((e.symm u : ↥KK) : Fin D → ZMod 2) := by
    intro u
    rw [show σ u = KK.subtype (e.symm u) from rfl, Submodule.subtype_apply]
  have hσ_proj : ∀ u : ↥(Submodule.map π ⊤), π (σ u) = (u : Fin D → ZMod 2) := by
    intro u
    rw [hσ_val u, ← he_val (e.symm u), LinearEquiv.apply_symm_apply]
  have hσ_mem : ∀ u : ↥(Submodule.map π ⊤), (u : Fin D → ZMod 2) ∈ Submodule.map π C →
      σ u ∈ C := by
    intro u hu
    have hσKK : σ u ∈ KK := by
      rw [hσ_val u]
      exact (e.symm u).2
    obtain ⟨c, hc, hcu⟩ := Submodule.mem_map.mp hu
    have hsub : σ u - c ∈ K0 := by
      rw [hK0, LinearMap.mem_ker]
      show π (σ u - c) = 0
      rw [map_sub, hσ_proj, hcu, sub_self]
    have hσU : σ u ∈ C ⊔ K0 := by
      have hσeq : σ u = c + (σ u - c) := by abel
      rw [hσeq]
      exact Submodule.add_mem _ (hle_C hc) (hle_K0 hsub)
    have hσKK' : σ u ∈ KC ⊔ W' := hKK ▸ hσKK
    obtain ⟨k, hk, w, hw, hkw⟩ := Submodule.mem_sup.mp hσKK'
    have hwU : w ∈ C ⊔ K0 := by
      have hwk : w = σ u - k := by rw [← hkw]; abel
      rw [hwk]
      exact Submodule.sub_mem _ hσU (hle_C (hKC_le_C hk))
    have hwbot : w ∈ (C ⊔ K0) ⊓ W' := ⟨hwU, hw⟩
    rw [hW'.inf_eq_bot] at hwbot
    have hw0 : w = 0 := by simpa using hwbot
    have hσ_eq : σ u = k := by rw [← hkw, hw0, add_zero]
    rw [hσ_eq]
    exact hKC_le_C hk
  let πW : (Fin D → ZMod 2) →ₗ[ZMod 2] ↥(Submodule.map π ⊤) :=
    π.codRestrict (Submodule.map π ⊤) (fun v => Submodule.mem_map.mpr ⟨v, trivial, rfl⟩)
  let T : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) := σ.comp πW
  refine ⟨⟨T, ?_, ?_, ?_⟩⟩
  · intro v k hk
    have h1 : π (T v) = π v := by
      show π (σ (πW v)) = π v
      rw [hσ_proj]
      rfl
    have h2 := congrFun h1 k
    rw [hπ] at h2
    simpa only [projA_apply, if_pos hk] using h2
  · intro v
    have hπv : πW (π v) = πW v := by
      apply Subtype.ext
      show π (π v) = π v
      rw [hπ]
      exact projA_idem A v
    show σ (πW v) = σ (πW (π v))
    rw [hπv]
  · intro c hc
    show σ (πW c) ∈ C
    apply hσ_mem
    exact Submodule.mem_map.mpr ⟨c, hc, rfl⟩

/-- If `a` is column-wise in `C` then so is `matExt A B (opVec T) w a`, where `T` is an
`A`-extension operator for `C`: the `l`-th column of the result is `T.toLin (∑ j ∈ B, w j l • col a j)`.
-/
theorem matExt_colwise {D : ℕ} {C : Submodule (ZMod 2) (Fin D → ZMod 2)} (A B : Finset (Fin D))
    (T : ExtOp C A) (w : Fin D → (Fin D → ZMod 2)) (a : Fin D × Fin D → ZMod 2)
    (ha : IsColwise C a) : IsColwise C (matExt A B (opVec T) w a) := by
  intro l
  have hTj : ∀ j, T.toLin (col a j) = ∑ i ∈ A, a (i, j) • opVec T i := by
    intro j
    rw [T.vanish (col a j), projA_eq_sum, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul]; simp only [col, opVec])
  have hcol : col (matExt A B (opVec T) w a) l = ∑ j ∈ B, w j l • T.toLin (col a j) := by
    funext k
    simp only [col, matExt_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hTj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcol]
  have hTsum : (∑ j ∈ B, w j l • T.toLin (col a j)) = T.toLin (∑ j ∈ B, w j l • col a j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => (map_smul T.toLin (w j l) (col a j)).symm)
  rw [hTsum]
  exact T.preserves _ (Submodule.sum_mem C (fun j _ => Submodule.smul_mem C _ (ha j)))

end GB

end Work.LT

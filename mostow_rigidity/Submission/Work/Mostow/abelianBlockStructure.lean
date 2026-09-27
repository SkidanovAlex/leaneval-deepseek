import Mathlib
import Submission.Work.Mostow.abelianBlockDefs
import Submission.Work.Mostow.jointEigenspacesCover
import Submission.Work.Mostow.blkT_isSymmetric_and_commute
import Submission.Work.Mostow.complexBlockStructure
import Submission.Work.Mostow.realBlockStructure
import Submission.Work.Mostow.opNorm_le_sum_of_orthogonalBlocks
import Submission.Work.Mostow.finrank_orthogonal_decomp
import Submission.Work.Mostow.two_le_finrank_of_complexStructure

/-!
# Simultaneous block structure of a finite abelian subgroup of `O(m)`

See `Work.Mostow.abelianBlockStructure` below.  The proof decomposes `E m = EuclideanSpace ℝ (Fin m)`
into the joint eigenspaces of the commuting symmetric family `blkT` attached to `B`
(`Work.Mostow.abelianBlockDefs`), classifies each block as "complex" (`Work.Mostow.complexBlockStructure`)
or "real" (`Work.Mostow.realBlockStructure`), and assembles the characters and the norm bound.
-/

namespace Work.Mostow

open scoped Classical

/-- The `ℝ`-dimension of a submodule is `0` iff the submodule is `⊥`. -/
private lemma finrank_bot_eq_zero {m : ℕ} :
    Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin m))) = 0 := by
  rw [Submodule.finrank_eq_zero]

/-- **Simultaneous block structure of a finite abelian subgroup of `O(m)`.**

For a finite abelian `B ≤ O(m)` there are `r`, `s` with `2 * r + s ≤ m`, complex characters
`χ i : B →* Circle` (`i : Fin r`, one per complex-conjugate pair of eigenvalues of the abelian
family) and sign characters `τ j : B →* Multiplicative (ZMod 2)` (`j : Fin s`, one per basis vector
of the "real" part), such that

* `(χ, τ)` is jointly injective,
* `‖(b : E m →L[ℝ] E m) - 1‖ ≤ ∑ i, ‖χ i b - 1‖ + ∑ j, (if τ j b = 1 then 0 else 2)` for every `b`.

(`‖(b : E m →L[ℝ] E m) - 1‖` is `Submission.Mostow.rotN b = Work.Mostow.mOf b` by `rfl`; do
`import Submission.Mostow.GeodDefs` and `import Submission.Work.Mostow.bieberbachDefs`.)

Route (simultaneous block decomposition of a commuting family of orthogonal maps).

1. `ι := B × Option B`; on `E m` consider the linear maps `T (b, none) := b + b⁻¹` and
   `T (b, some b') := (b - b⁻¹) * (b' - b'⁻¹)` (composition).  Each `T i` is symmetric
   (`LinearMap.IsSymmetric`) and they commute pairwise; use
   `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`
   (`Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean`) or the workspace wrapper
   `Work.Mostow.jointEigenspacesCover`
   (`Submission/Work/Mostow/jointEigenspacesCover.lean`).  `iSup` over the *finite* set of
   eigenvalues, or over all of `ι → ℝ` (all but finitely many joint eigenspaces are `⊥`).
2. Blocks are the joint eigenspaces `W = ⨅ i, eigenspace (T i) (λ i)`; they are pairwise
   orthogonal and span, so `∑ dim W = m`, and every `b` preserves each `W`.
3. On a block `W ≠ ⊥` put `λb := λ (b, none)` (so `(b + b⁻¹)|_W = λb • 1`) and
   `μ (b,b') := λ (b, some b')` (so `(b - b⁻¹)(b' - b'⁻¹)|_W = μ (b,b') • 1`).  Show `|λb| ≤ 2`,
   write `λb = 2 cos θb` with `θb ∈ [0,π]`, and deduce `(b - b⁻¹)²|_W = (λb² - 4) • 1`; for
   `sin θb ≠ 0` the map `Jb := (b - b⁻¹) / (2 sin θb)` on `W` satisfies `Jb² = -1` and is
   orthogonal (and antisymmetric).
4. If some `b₀` has `sin θ_{b₀} ≠ 0`, then for every `b` with `sin θb ≠ 0` the product `Jb * Jb₀` is
   the scalar `μ (b,b₀) / (4 sin θb sin θ_{b₀})` on `W` and is orthogonal, hence `= ± 1`; so
   `Jb = εb • Jb₀` with `εb = ±1` (the `±` may depend on `b` — that is fine).  For `sin θb = 0` one
   has `b = ±1` on `W`, so `b x = cos θb • x + sin θb * εb • (Jb₀ x)` with any `εb`.  Hence for all
   `b` there is `εb ∈ {±1}` with `b|_W = cos θb • 1 + sin θb * εb • Jb₀`.
   Then `z b := cos θb + εb * sin θb * Complex.I : ℂ` satisfies `|z b| = 1`; and `z` is
   multiplicative: expanding `(cos θb + sin θb εb Jb₀) * (cos θb' + sin θb' εb' Jb₀)` using
   `Jb₀² = -1` shows that the real part of that product is `cos θ_{bb'}` and its `Jb₀`-coefficient
   is `sin θ_{bb'} ε_{bb'}`, which is exactly `z (b * b') = z b * z b'` (both sides have the same
   real part and the same coefficient of `I`).  These are the `r` "complex" blocks; each has even
   dimension (`Jb₀² = -1` makes `W` a `ℂ`-vector space, so `finrank ℝ W = 2 * finrank ℂ W ≥ 2`).
   The operator-norm contribution of the block is exactly `‖χ b - 1‖`, because
   `(b - 1) x = (cos θb - 1) • x + sin θb * εb • (Jb₀ x)`, an orthogonal sum of two vectors of
   lengths `|cos θb - 1|` and `|sin θb|`, so its norm is `‖z b - 1‖`.
5. If `sin θb = 0` for all `b` on a block, then every `b` acts on it by `±1` (`λb = 2` forces
   `b x = x`: `⟨b x, x⟩ = ‖x‖² = ‖b x‖ ‖x‖` and Cauchy–Schwarz; `λb = -2` forces `b x = -x`);
   picking an orthonormal basis of `W` gives `dim W` sign characters `B →* Multiplicative (ZMod 2)`.
   `s := ∑ dim W` over these "sign" blocks; each such block also contributes `dim W` to the identity
   `2 * r + s ≤ m`.
6. Injectivity: all `χ i b = 1` and all `τ j b = 1` forces `b` to act as the identity on every
   block, hence `b = 1`.
7. `2 * r + s ≤ m` since the blocks partition `E m` and every complex block has dimension `≥ 2`.
8. Norm control: `b - 1` is block diagonal for the orthogonal decomposition, so its operator norm
   is the maximum of the block operator norms (the blocks being pairwise orthogonal and spanning
   makes `‖b - 1‖ = max_W ‖(b - 1)|_W‖`), which is at most the sum of the per-block contributions.

Helper lemmas in the delegated file are welcome; only the final `abelianBlockStructure` need have
the shape above. -/
theorem abelianBlockStructure (m : ℕ)
    (B : Subgroup (EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))) [Finite B]
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ∃ (r s : ℕ) (χ : Fin r → B →* Circle) (τ : Fin s → B →* Multiplicative (ZMod 2)),
      2 * r + s ≤ m ∧
      (∀ b : B, (∀ i, χ i b = 1) → (∀ j, τ j b = 1) → b = 1) ∧
      (∀ b : B, ‖((b : B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) - 1‖
        ≤ (∑ i : Fin r, ‖(((χ i b) : Circle) : ℂ) - 1‖)
          + (∑ j : Fin s, if τ j b = 1 then (0 : ℝ) else 2)) := by
  classical
  haveI hBfin : Fintype ↥B := Fintype.ofFinite ↥B
  -- ## Step 1: the commuting symmetric family `blkT` and its joint eigenspaces
  have hsymm : ∀ i : ↥B × Option ↥B, (blkT i).IsSymmetric :=
    (blkT_isSymmetric_and_commute hcomm).1
  have hpair : Pairwise (Function.onFun Commute (fun i : ↥B × Option ↥B => blkT i)) :=
    (blkT_isSymmetric_and_commute hcomm).2.1
  have hpair' : ∀ i j : ↥B × Option ↥B, i ≠ j → Commute (blkT i) (blkT j) :=
    fun i j h => @hpair i j h
  have hcb : ∀ (i : ↥B × Option ↥B) (b : ↥B),
      Commute (blkT i) ((b : ↥B) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :=
    (blkT_isSymmetric_and_commute hcomm).2.2
  obtain ⟨eig, heig, hspan0, horth0⟩ :=
    jointEigenspacesCover (fun i : ↥B × Option ↥B => blkT i) hsymm
      (fun i j => if h : i = j then h ▸ Commute.refl (blkT i) else hpair' i j h)
  let η : Type _ := ((i : ↥B × Option ↥B) → ↥(Set.range (eig i)))
  haveI hηfin : Fintype η :=
    (inferInstance : Fintype ((i : ↥B × Option ↥B) → ↥(Set.range (eig i))))
  let Pal : η → Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
    fun j => ⨅ i, Module.End.eigenspace (blkT i) (j i)
  have hspan : (⨆ j : η, Pal j) = ⊤ := hspan0
  have horth : ∀ j j' : η, j ≠ j' → ∀ x ∈ Pal j, ∀ y ∈ Pal j', inner ℝ x y = 0 := horth0
  have hmem : ∀ (j : η) (i : ↥B × Option ↥B) (x : EuclideanSpace ℝ (Fin m)),
      x ∈ Pal j → blkT i x = ((j i : ℝ)) • x := by
    intro j i x hx
    exact Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf (fun i => Module.End.eigenspace (blkT i) (j i))).mp hx i)
  have hb_mem : ∀ (j : η) (b : ↥B) (x : EuclideanSpace ℝ (Fin m)),
      x ∈ Pal j →
        ((b : ↥B) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) x ∈ Pal j := by
    intro j b x hx
    refine (Submodule.mem_iInf (fun i => Module.End.eigenspace (blkT i) (j i))).mpr (fun i => ?_)
    rw [Module.End.mem_eigenspace_iff]
    have hcomm_i : (blkT i)
        (((b : ↥B) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) x)
        = ((b : ↥B) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ((blkT i) x) := by
      have h := hcb i b
      exact congrFun (congrArg DFunLike.coe h.eq) x
    rw [hcomm_i, hmem j i x hx, map_smul]
  -- the scalar eigenvalues of `b + b⁻¹` and of `(b - b⁻¹)(b' - b'⁻¹)` on each block
  let lam : (j : η) → ↥B → ℝ := fun j b => ((j (b, none) : ℝ))
  let mmu : (j : η) → ↥B → ↥B → ℝ := fun j b b' => ((j (b, some b') : ℝ))
  have hscal : ∀ (j : η) (b : ↥B), ∀ x ∈ Pal j,
      oSym ((b : ↥B) : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x
        = lam j b • x := by
    intro j b x hx
    exact hmem j (b, none) x hx
  have hmuscal : ∀ (j : η) (b b' : ↥B), ∀ x ∈ Pal j,
      (oSk ((b : ↥B) : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
        * oSk ((b' : ↥B) : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))) x
          = mmu j b b' • x := by
    intro j b b' x hx
    exact hmem j (b, some b') x hx
  have hscal_unique : ∀ (j : η) (b : ↥B) (a : ℝ), Pal j ≠ ⊥ →
      (∀ x ∈ Pal j, oSym ((b : ↥B) : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x
        = a • x) → a = lam j b := by
    intro j b a hne ha
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff (Pal j)).mp hne
    have h1 : oSym ((b : ↥B) : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x
        = a • x := ha x hx
    have h3 : (a - lam j b) • x = 0 := by rw [sub_smul, ← h1, hscal j b x hx, sub_self]
    have h4 : a - lam j b = 0 := by
      rcases smul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h hx0
    linarith
  let comp : η → Prop := fun j => Pal j ≠ ⊥ ∧ ∃ b : ↥B, (lam j b) ^ 2 < 4
  let real : η → Prop := fun j => Pal j ≠ ⊥ ∧ ¬ ∃ b : ↥B, (lam j b) ^ 2 < 4
  have hreal_not_comp : ∀ j : η, real j → ¬ comp j := by
    intro j hj hj2
    exact hj.2 hj2.2
  have hbot_of : ∀ j : η, ¬ comp j → ¬ real j → Pal j = ⊥ := by
    intro j h1 h2
    by_contra hne
    exact h2 ⟨hne, fun ⟨b, hb⟩ => h1 ⟨hne, ⟨b, hb⟩⟩⟩
  -- ## Step 2: complex block data
  have hex_cplx : ∀ (j : η) (hj : comp j),
      ∃ (J : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (z : ↥B →* Circle),
      (∀ x ∈ Pal j, J (J x) = -x) ∧ (∀ x ∈ Pal j, ‖J x‖ = ‖x‖) ∧ (∀ x ∈ Pal j, J x ∈ Pal j) ∧
      (∀ (b : ↥B) (x : EuclideanSpace ℝ (Fin m)), x ∈ Pal j →
        (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x
          = (((z b : Circle) : ℂ).re) • x + (((z b : Circle) : ℂ).im) • (J x)) ∧
      (∀ (b : ↥B) (x : EuclideanSpace ℝ (Fin m)), x ∈ Pal j →
        ‖(b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x - x‖
          ≤ ‖(((z b : Circle) : ℂ) - 1)‖ * ‖x‖) := by
    intro j hj
    obtain ⟨hne, b0⟩ := hj
    obtain ⟨b₀, ha₀⟩ := b0
    exact complexBlockStructure (ρ := B.subtype) (Pal j) hne (fun g x hx => hb_mem j g x hx)
      (fun g => ⟨lam j g, fun x hx => hscal j g x hx⟩)
      (fun g g' => ⟨mmu j g g', fun x hx => hmuscal j g g' x hx⟩)
      ⟨b₀, lam j b₀, fun x hx => hscal j b₀ x hx, ha₀⟩
  -- ## Step 3: real block data
  have hex_real : ∀ (j : η) (hj : real j),
      ∃ t : ↥B →* Multiplicative (ZMod 2), ∀ (b : ↥B) (x : EuclideanSpace ℝ (Fin m)), x ∈ Pal j →
        (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x
            = (if t b = 1 then x else -x) ∧
        ‖(b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x - x‖
            = (if t b = 1 then (0:ℝ) else 2) * ‖x‖ := by
    intro j hj
    refine realBlockStructure (ρ := B.subtype) (Pal j) hj.1 (fun g x hx => hb_mem j g x hx)
      (fun g => ⟨lam j g, fun x hx => hscal j g x hx⟩) (fun g hcon => ?_)
    obtain ⟨a, ha, ha2⟩ := hcon
    exact hj.2 ⟨g, by rw [← hscal_unique j g a hj.1 ha]; exact ha2⟩
  -- ## Step 4: choose the data and build the characters
  let Jf : (j : η) → comp j → EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun j hj => Classical.choose (hex_cplx j hj)
  let zf : (j : η) → comp j → ↥B →* Circle :=
    fun j hj => Classical.choose (Classical.choose_spec (hex_cplx j hj))
  have hzf : ∀ (j : η) (hj : comp j),
      (∀ x ∈ Pal j, Jf j hj (Jf j hj x) = -x) ∧ (∀ x ∈ Pal j, ‖Jf j hj x‖ = ‖x‖) ∧
      (∀ x ∈ Pal j, Jf j hj x ∈ Pal j) ∧
      (∀ (b : ↥B) (x : EuclideanSpace ℝ (Fin m)), x ∈ Pal j →
        (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x
          = (((zf j hj b : Circle) : ℂ).re) • x + (((zf j hj b : Circle) : ℂ).im) • (Jf j hj x)) ∧
      (∀ (b : ↥B) (x : EuclideanSpace ℝ (Fin m)), x ∈ Pal j →
        ‖(b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x - x‖
          ≤ ‖(((zf j hj b : Circle) : ℂ) - 1)‖ * ‖x‖) :=
    fun j hj => Classical.choose_spec (Classical.choose_spec (hex_cplx j hj))
  let tf : (j : η) → real j → ↥B →* Multiplicative (ZMod 2) :=
    fun j hj => Classical.choose (hex_real j hj)
  have htf : ∀ (j : η) (hj : real j), ∀ (b : ↥B) (x : EuclideanSpace ℝ (Fin m)), x ∈ Pal j →
      (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x
          = (if tf j hj b = 1 then x else -x) ∧
      ‖(b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x - x‖
          = (if tf j hj b = 1 then (0:ℝ) else 2) * ‖x‖ :=
    fun j hj => Classical.choose_spec (hex_real j hj)
  let Ac : Finset η := Finset.univ.filter comp
  let Rc : Finset η := Finset.univ.filter real
  have memAc : ∀ (j : η), comp j → j ∈ Ac := fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have memRc : ∀ (j : η), real j → j ∈ Rc := fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have comp_of_mem : ∀ {j : η}, j ∈ Ac → comp j := fun h => (Finset.mem_filter.mp h).2
  have notComp_of_notMem : ∀ {j : η}, j ∉ Ac → ¬ comp j := fun {j} hj hc => hj (memAc j hc)
  have notReal_of_notMem : ∀ {j : η}, j ∉ Rc → ¬ real j := fun {j} hj hr => hj (memRc j hr)
  have real_of_mem : ∀ {j : η}, j ∈ Rc → real j := fun h => (Finset.mem_filter.mp h).2
  haveI hAfin : Fintype {j : η // j ∈ Ac} := inferInstance
  haveI hRfin : Fintype {j : η // j ∈ Rc} := inferInstance
  let eA : ↥Ac ≃ Fin Ac.card := Finset.equivFin Ac
  let eR : ↥Rc ≃ Fin Rc.card := Finset.equivFin Rc
  let χη : η → ↥B →* Circle := fun j => if hj : comp j then zf j hj else 1
  let τη : η → ↥B →* Multiplicative (ZMod 2) := fun j => if hj : real j then tf j hj else 1
  let χ : Fin Ac.card → ↥B →* Circle := fun i => χη (eA.symm i).1
  let τ : Fin Rc.card → ↥B →* Multiplicative (ZMod 2) := fun i => τη (eR.symm i).1
  have hχη_comp : ∀ (j : η) (hj : comp j), χη j = zf j hj := fun j hj => dif_pos hj
  have hχη_not : ∀ (j : η), ¬ comp j → χη j = 1 := fun j hj => dif_neg hj
  have hτη_real : ∀ (j : η) (hj : real j), τη j = tf j hj := fun j hj => dif_pos hj
  have hτη_not : ∀ (j : η), ¬ real j → τη j = 1 := fun j hj => dif_neg hj
  have hχη_not_val : ∀ (j : η), ¬ comp j → ∀ c : ↥B, (χη j) c = (1 : Circle) := fun j hj c => by
    have h1 : χη j = (1 : ↥B →* Circle) := hχη_not j hj
    rw [h1]
    rfl
  have hτη_not_val : ∀ (j : η), ¬ real j → ∀ c : ↥B,
      (τη j) c = (1 : Multiplicative (ZMod 2)) := fun j hj c => by
    have h1 : τη j = (1 : ↥B →* Multiplicative (ZMod 2)) := hτη_not j hj
    rw [h1]
    rfl
  have hχ_eA : ∀ a : ↥Ac, χ (eA a) = χη a.1 := by
    intro a
    rw [show χ (eA a) = χη (eA.symm (eA a)).1 from rfl, Equiv.symm_apply_apply]
  have hτ_eR : ∀ a : ↥Rc, τ (eR a) = τη a.1 := by
    intro a
    rw [show τ (eR a) = τη (eR.symm (eR a)).1 from rfl, Equiv.symm_apply_apply]
  have hχsumE : ∀ b : ↥B, (∑ i : Fin Ac.card, ‖(((χ i b) : Circle) : ℂ) - 1‖)
      = ∑ j ∈ Ac, ‖(((χη j b) : Circle) : ℂ) - 1‖ := by
    intro b
    rw [← Equiv.sum_comp eA (fun i : Fin Ac.card => ‖(((χ i b) : Circle) : ℂ) - 1‖)]
    rw [Finset.sum_subtype (p := fun j : η => j ∈ Ac) Ac (by intro x; exact Iff.rfl)
      (fun j => ‖(((χη j b) : Circle) : ℂ) - 1‖)]
    apply Finset.sum_congr rfl
    intro a _
    rw [hχ_eA a]
  have hτsumE : ∀ b : ↥B, (∑ i : Fin Rc.card, (if τ i b = 1 then (0:ℝ) else 2))
      = ∑ j ∈ Rc, (if τη j b = 1 then (0:ℝ) else 2) := by
    intro b
    rw [← Equiv.sum_comp eR (fun i : Fin Rc.card => (if τ i b = 1 then (0:ℝ) else 2))]
    rw [Finset.sum_subtype (p := fun j : η => j ∈ Rc) Rc (by intro x; exact Iff.rfl)
      (fun j => (if τη j b = 1 then (0:ℝ) else 2))]
    apply Finset.sum_congr rfl
    intro a _
    rw [hτ_eR a]
  -- ## Step 5: the three conclusions
  refine ⟨Ac.card, Rc.card, χ, τ, ?_, ?_, ?_⟩
  · -- `2 * r + s ≤ m`
    have hdim : ∑ j : η, Module.finrank ℝ ↥(Pal j) = m := by
      rw [finrank_orthogonal_decomp Pal horth hspan, finrank_euclideanSpace, Fintype.card_fin]
    have hcomp2 : ∀ j ∈ Ac, 2 ≤ Module.finrank ℝ ↥(Pal j) := fun j hj =>
      two_le_finrank_of_complexStructure (Pal j) (Jf j (comp_of_mem hj)) (comp_of_mem hj).1
        (fun x hx => (hzf j (comp_of_mem hj)).2.2.1 x hx)
        (fun x hx => (hzf j (comp_of_mem hj)).1 x hx)
    have hreal1 : ∀ j ∈ Rc, 1 ≤ Module.finrank ℝ ↥(Pal j) := fun j hj => by
      have hnt : Nontrivial ↥(Pal j) := by
        obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff (Pal j)).mp (real_of_mem hj).1
        exact ⟨⟨x, hx⟩, ⟨0, (Pal j).zero_mem⟩, by simpa using hx0⟩
      have hpos : 0 < Module.finrank ℝ ↥(Pal j) := Module.finrank_pos_iff.mpr hnt
      omega
    have hcard2 : 2 * Ac.card = ∑ j ∈ Ac, (2:ℕ) := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      simp
    have hcard1 : Rc.card = ∑ j ∈ Rc, (1:ℕ) := by
      rw [Finset.card_eq_sum_ones]
    have hdisj : Disjoint Ac Rc := Finset.disjoint_left.mpr (fun j hjA hjR =>
      hreal_not_comp j (real_of_mem hjR) (comp_of_mem hjA))
    have hunion : (∑ j ∈ Ac ∪ Rc, Module.finrank ℝ ↥(Pal j))
        = (∑ j ∈ Ac, Module.finrank ℝ ↥(Pal j)) + (∑ j ∈ Rc, Module.finrank ℝ ↥(Pal j)) :=
      Finset.sum_union hdisj
    have hsub : (∑ j ∈ Ac ∪ Rc, Module.finrank ℝ ↥(Pal j)) ≤ m := by
      have h1 : (∑ j ∈ Ac ∪ Rc, Module.finrank ℝ ↥(Pal j))
          ≤ ∑ j ∈ Finset.univ, Module.finrank ℝ ↥(Pal j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => Nat.zero_le _)
      rwa [hdim] at h1
    have hle1 : 2 * Ac.card ≤ ∑ j ∈ Ac, Module.finrank ℝ ↥(Pal j) := by
      rw [hcard2]
      exact Finset.sum_le_sum hcomp2
    have hle2 : Rc.card ≤ ∑ j ∈ Rc, Module.finrank ℝ ↥(Pal j) := by
      rw [hcard1]
      exact Finset.sum_le_sum hreal1
    calc 2 * Ac.card + Rc.card
        ≤ (∑ j ∈ Ac, Module.finrank ℝ ↥(Pal j)) + (∑ j ∈ Rc, Module.finrank ℝ ↥(Pal j)) :=
          add_le_add hle1 hle2
      _ = ∑ j ∈ Ac ∪ Rc, Module.finrank ℝ ↥(Pal j) := hunion.symm
      _ ≤ m := hsub
  · -- injectivity
    intro b hχ hτ
    have hfix : ∀ x : EuclideanSpace ℝ (Fin m),
        ((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) x = x := by
      intro x
      have hx : x ∈ ⨆ j : η, Pal j := by rw [hspan]; trivial
      refine Submodule.iSup_induction (p := Pal)
        (motive := fun x => ((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) x = x)
        hx ?_ ?_ ?_
      · intro j y hy
        by_cases hj : comp j
        · have hzj : zf j hj b = 1 := by
            have h1 := hχ (eA ⟨j, memAc j hj⟩)
            rw [hχ_eA] at h1
            rwa [hχη_comp j hj] at h1
          have hgoal : ((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) y
              = (((zf j hj b : Circle) : ℂ).re) • y
                + (((zf j hj b : Circle) : ℂ).im) • (Jf j hj y) :=
            (hzf j hj).2.2.2.1 b y hy
          rw [hgoal, hzj]
          simp
        · by_cases hj2 : real j
          · have htj : tf j hj2 b = 1 := by
              have h1 := hτ (eR ⟨j, memRc j hj2⟩)
              rw [hτ_eR] at h1
              rwa [hτη_real j hj2] at h1
            have hgoal : ((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) y
                = (if tf j hj2 b = 1 then y else -y) := (htf j hj2 b y hy).1
            rw [hgoal, htj]
            simp
          · have hbot : Pal j = ⊥ := hbot_of j hj hj2
            rw [hbot] at hy
            rw [(Submodule.mem_bot ℝ).mp hy]
            simp
      · simp
      · intro y z hy hz
        rw [map_add, hy, hz]
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro x
    simpa using hfix x
  · -- norm bound
    intro b
    let cB : η → ℝ := fun j =>
      ‖(((χη j b) : Circle) : ℂ) - 1‖ + (if τη j b = 1 then (0:ℝ) else 2)
    have hcB0 : ∀ j : η, 0 ≤ cB j := fun j =>
      add_nonneg (norm_nonneg _) (by split <;> norm_num)
    have hbnd : ∀ j : η, ∀ x ∈ Pal j,
        ‖(((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) - 1) x‖
          ≤ cB j * ‖x‖ := by
      intro j x hx
      have hsub : (((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) - 1) x
          = ((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) x - x := by
        rw [sub_apply, one_apply_eq_self]
      have hgoal : ((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) x - x
          = (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) x - x := rfl
      rw [hsub, hgoal]
      by_cases hj : comp j
      · have hnotR : ¬ real j := fun h => hreal_not_comp j h hj
        have h0 : (τη j) b = (1 : Multiplicative (ZMod 2)) := hτη_not_val j hnotR b
        have hcB : cB j = ‖(((zf j hj b) : Circle) : ℂ) - 1‖ := by
          rw [show cB j = ‖(((χη j b) : Circle) : ℂ) - 1‖
                + (if τη j b = 1 then (0:ℝ) else 2) from rfl, hχη_comp j hj, h0,
            if_pos rfl, add_zero]
        rw [hcB]
        exact (hzf j hj).2.2.2.2 b x hx
      · by_cases hj2 : real j
        · have h0 : ‖(((χη j b) : Circle) : ℂ) - 1‖ = 0 := by
            rw [hχη_not_val j hj b, Circle.coe_one, sub_self, norm_zero]
          have hcB : cB j = (if tf j hj2 b = 1 then (0:ℝ) else 2) := by
            rw [show cB j = ‖(((χη j b) : Circle) : ℂ) - 1‖
                  + (if τη j b = 1 then (0:ℝ) else 2) from rfl, h0, zero_add, hτη_real j hj2]
          rw [hcB]
          exact le_of_eq (htf j hj2 b x hx).2
        · have hbot : Pal j = ⊥ := hbot_of j hj hj2
          rw [hbot] at hx
          rw [(Submodule.mem_bot ℝ).mp hx]
          have h0 : ‖(((χη j b) : Circle) : ℂ) - 1‖ = 0 := by
            rw [hχη_not_val j hj b, Circle.coe_one, sub_self, norm_zero]
          have h1 : (τη j) b = (1 : Multiplicative (ZMod 2)) := hτη_not_val j hj2 b
          have hcB : cB j = 0 := by
            rw [show cB j = ‖(((χη j b) : Circle) : ℂ) - 1‖
                  + (if τη j b = 1 then (0:ℝ) else 2) from rfl, h0, h1, if_pos rfl, zero_add]
          rw [hcB]
          simp
    have hTmem : ∀ j : η, ∀ x ∈ Pal j,
        (((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) - 1) x ∈ Pal j := by
      intro j x hx
      have hsub : (((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) - 1) x
          = ((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) x - x := by
        rw [sub_apply, one_apply_eq_self]
      rw [hsub]
      exact (Pal j).sub_mem (hb_mem j b x hx) hx
    have hKey := opNorm_le_sum_of_orthogonalBlocks Pal horth hspan
      (((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) - 1)
      hTmem cB hcB0 hbnd
    have hsumχ : (∑ j : η, ‖(((χη j b) : Circle) : ℂ) - 1‖)
        = ∑ j ∈ Ac, ‖(((χη j b) : Circle) : ℂ) - 1‖ :=
      (Finset.sum_subset (Finset.filter_subset comp Finset.univ)
        (fun j _ hj => by
          have h1 : (χη j) b = (1 : Circle) := hχη_not_val j (notComp_of_notMem hj) b
          rw [h1]
          simp)).symm
    have hsumτ : (∑ j : η, (if τη j b = 1 then (0:ℝ) else 2))
        = ∑ j ∈ Rc, (if τη j b = 1 then (0:ℝ) else 2) :=
      (Finset.sum_subset (Finset.filter_subset real Finset.univ)
        (fun j _ hj => by
          have h1 : (τη j) b = (1 : Multiplicative (ZMod 2)) := hτη_not_val j (notReal_of_notMem hj) b
          rw [h1]
          simp)).symm
    have hsum : (∑ j : η, cB j) = (∑ i : Fin Ac.card,
          ‖(((χ i b) : Circle) : ℂ) - 1‖)
        + (∑ i : Fin Rc.card, (if τ i b = 1 then (0:ℝ) else 2)) := by
      have h1 : (∑ j : η, cB j) = (∑ j : η, ‖(((χη j b) : Circle) : ℂ) - 1‖)
          + (∑ j : η, (if τη j b = 1 then (0:ℝ) else 2)) :=
        Finset.sum_add_distrib
      have h4 : (∑ j ∈ Ac, ‖(((χη j b) : Circle) : ℂ) - 1‖)
          = (∑ i : Fin Ac.card, ‖(((χ i b) : Circle) : ℂ) - 1‖) := (hχsumE b).symm
      have h5 : (∑ j ∈ Rc, (if τη j b = 1 then (0:ℝ) else 2))
          = (∑ i : Fin Rc.card, (if τ i b = 1 then (0:ℝ) else 2)) := (hτsumE b).symm
      have h2 : (∑ j : η, ‖(((χη j b) : Circle) : ℂ) - 1‖)
          + (∑ j : η, (if τη j b = 1 then (0:ℝ) else 2))
          = (∑ i : Fin Ac.card, ‖(((χ i b) : Circle) : ℂ) - 1‖)
            + (∑ i : Fin Rc.card, (if τ i b = 1 then (0:ℝ) else 2)) := by
        rw [hsumχ, hsumτ, h4, h5]
      exact h1.trans h2
    have hop : ‖(((b : ↥B) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) - 1)‖
        ≤ ∑ j : η, cB j :=
      ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun j _ => hcB0 j)) hKey
    exact hop.trans (le_of_eq hsum)

end Work.Mostow

import Mathlib
import Submission.Work.SSSR.KunnethEZ.EZGenX
import Submission.Work.SSSR.KunnethEZ.ezChain_isCycle

variable {R : Type} [CommRing R] [Nontrivial R]

set_option maxHeartbeats 4000000
set_option autoImplicit false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial
namespace Work.SSSR.KunnethEZ

open Work.SSSR.Cohomology.Crux33
noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- `finCongr` preserves the underlying value. -/
lemma finCongr_val {n m : ℕ} (h : n = m) (k : Fin n) : ((finCongr h) k).val = k.val := by
  cases h; simp

/-- `eqToHom` between two standard simplices preserves the underlying value. -/
lemma eqToHom_simplex_val {n m : ℕ} (h : n = m) (k : Fin (n+1)) :
    ((eqToHom (congrArg SimplexCategory.mk h) : ⦋n⦌ ⟶ ⦋m⦌) k).val = k.val := by
  cases h; simp

/-- The `E`-count `ANat` is invariant under the `finCongr` reindexing of a shuffle. -/
lemma ANat_finsetCongr {n m : ℕ} (h : n = m) (S : Finset (Fin n)) (r : ℕ) :
    ANat ((finCongr h).finsetCongr S) r = ANat S r := by
  rw [ANat, ANat, Equiv.finsetCongr_apply]
  have hmap : (Finset.univ : Finset (Fin m)).filter (fun j => j.val < r) \
        Finset.map (finCongr h).toEmbedding S
      = Finset.map (finCongr h).toEmbedding
          ((Finset.univ : Finset (Fin n)).filter (fun j => j.val < r) \ S) := by
    rw [← Finset.map_univ_equiv (finCongr h), Finset.filter_map, Finset.map_sdiff]
    rw [show Finset.filter ((fun j : Fin m => j.val < r) ∘ ⇑(finCongr h).toEmbedding)
          (Finset.univ : Finset (Fin n))
        = Finset.filter (fun j : Fin n => j.val < r) Finset.univ from
      Finset.filter_congr (fun x _ => by
        simp only [Function.comp_apply, Equiv.coe_toEmbedding, finCongr_val])]
  rw [hmap, Finset.card_map]

/-- The `N`-count `BNat` is invariant under the `finCongr` reindexing of a shuffle. -/
lemma BNat_finsetCongr {n m : ℕ} (h : n = m) (S : Finset (Fin n)) (r : ℕ) :
    BNat ((finCongr h).finsetCongr S) r = BNat S r := by
  rw [BNat, BNat, Equiv.finsetCongr_apply, Finset.filter_map]
  rw [show Finset.filter ((fun j : Fin m => j.val < r) ∘ ⇑(finCongr h).toEmbedding) S
      = Finset.filter (fun j : Fin n => j.val < r) S from
    Finset.filter_congr (fun x _ => by
      simp only [Function.comp_apply, Equiv.coe_toEmbedding, finCongr_val])]
  rw [Finset.card_map]

/-- The inversion count `invCountN` is invariant under the `finCongr` reindexing. -/
lemma invCountN_finsetCongr {n m : ℕ} (h : n = m) (S : Finset (Fin n)) :
    invCountN ((finCongr h).finsetCongr S) = invCountN S := by
  rw [invCountN, invCountN, Equiv.finsetCongr_apply]
  have hsdiff : (Finset.univ : Finset (Fin m)) \ Finset.map (finCongr h).toEmbedding S
      = Finset.map (finCongr h).toEmbedding ((Finset.univ : Finset (Fin n)) \ S) := by
    rw [← Finset.map_univ_equiv (finCongr h), Finset.map_sdiff]
  rw [hsdiff, Finset.sum_map]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show BNat (Finset.map (finCongr h).toEmbedding S) ((finCongr h).toEmbedding k).val
      = BNat ((finCongr h).finsetCongr S) ((finCongr h).toEmbedding k).val from by
        rw [Equiv.finsetCongr_apply]]
  rw [BNat_finsetCongr, Equiv.toEmbedding_apply, finCongr_val]

/-- The transport of the generator `genP R` of a pair of simplices along an equality of bidegrees. -/
lemma eqToHom_genP {X Y : SSet} {a b : ℕ} (h : a = b) (x : X _⦋a⦌) (y : Y _⦋a⦌) :
    (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (eZR R)).X k) h)).hom (genP R x y)
      = genP R (X.map (eqToHom (congrArg SimplexCategory.mk h.symm)).op x)
             (Y.map (eqToHom (congrArg SimplexCategory.mk h.symm)).op y) := by
  subst h
  simp [genP]

/-- The reindexing equivalence `PShuffle (p-1) q ≃ Sh23 p q` given by `finCongr`. -/
def shuffleEquiv (p q : ℕ) (h : (p-1)+q = p+q-1) : Sh23 p q ≃ PShuffle (p-1) q where
  toFun T := ⟨(finCongr h.symm).finsetCongr T.1, by
    rw [Equiv.finsetCongr_apply, Finset.card_map]; exact T.2⟩
  invFun S := ⟨(finCongr h).finsetCongr S.1, by
    rw [Equiv.finsetCongr_apply, Finset.card_map]; exact S.2⟩
  left_inv T := by
    ext1
    show (finCongr h).finsetCongr ((finCongr h.symm).finsetCongr T.1) = T.1
    rw [Equiv.finsetCongr_apply, Equiv.finsetCongr_apply, Finset.map_map]
    ext x; simp
  right_inv S := by
    ext1
    show (finCongr h.symm).finsetCongr ((finCongr h).finsetCongr S.1) = S.1
    rw [Equiv.finsetCongr_apply, Equiv.finsetCongr_apply, Finset.map_map]
    ext x; simp

/-- The reindexing map on the `Sh23` side. -/
noncomputable abbrev ez23Map (p q : ℕ) (h : (p-1)+q = p+q-1) (S : PShuffle (p-1) q) : Sh23 p q :=
  (shuffleEquiv p q h).symm S

/-- `aMap23` is the composite of `aHom` with the `eqToHom` bridging the two bidegrees. -/
lemma ez23Map_aHom (p q : ℕ) (h : (p-1)+q = p+q-1) (S : PShuffle (p-1) q) :
    (eqToHom (congrArg SimplexCategory.mk h.symm) : ⦋p+q-1⦌ ⟶ ⦋(p-1)+q⦌) ≫ aHom S.1 S.2
      = aMap23 p q (ez23Map p q h S) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  apply Fin.ext
  show (((eqToHom (congrArg SimplexCategory.mk h.symm) : ⦋p+q-1⦌ ⟶ ⦋(p-1)+q⦌) ≫ aHom S.1 S.2) k).val
     = ((aMap23 p q (ez23Map p q h S)) k).val
  rw [comp_val, aHom_val, ← pANat_apply, eqToHom_simplex_val, pANat_eq_ANat, aMap23_apply]
  case h => exact h.symm
  exact (ANat_finsetCongr h S.1 (↑k)).symm

/-- `bMap23` is the composite of `bHom` with the `eqToHom` bridging the two bidegrees. -/
lemma ez23Map_bHom (p q : ℕ) (h : (p-1)+q = p+q-1) (S : PShuffle (p-1) q) :
    (eqToHom (congrArg SimplexCategory.mk h.symm) : ⦋p+q-1⦌ ⟶ ⦋(p-1)+q⦌) ≫ bHom S.1 S.2
      = bMap23 p q (ez23Map p q h S) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  apply Fin.ext
  show (((eqToHom (congrArg SimplexCategory.mk h.symm) : ⦋p+q-1⦌ ⟶ ⦋(p-1)+q⦌) ≫ bHom S.1 S.2) k).val
     = ((bMap23 p q (ez23Map p q h S)) k).val
  rw [comp_val, bHom_val, ← pBNat_apply, eqToHom_simplex_val, pBNat_eq_BNat, bMap23_apply]
  case h => exact h.symm
  exact (BNat_finsetCongr h S.1 (↑k)).symm

/-- `shufSignN` on the reindexed shuffle is `shufSign`. -/
lemma ez23Map_sign (p q : ℕ) (h : (p-1)+q = p+q-1) (S : PShuffle (p-1) q) :
    shufSign S.1 = shufSignN (ez23Map p q h S).1 := by
  rw [shufSign_eq_shufSignN, shufSignN, shufSignN]
  congr 1
  rw [show (ez23Map p q h S).1 = (finCongr h).finsetCongr S.1 from rfl]
  exact (invCountN_finsetCongr h S.1).symm

/-- **The `Sh23`-indexed shuffle chain is the `(p-1,q)` Eilenberg–Zilber shuffle chain.** -/
theorem ez23_eq_ezGen (p q : ℕ) (hp : 1 ≤ p) (X Y : SSet) (h : (p-1)+q = p+q-1)
    (σ : X _⦋p-1⦌) (τ : Y _⦋q⦌) :
    (∑ T : Sh23 p q, shufSignN T.1 •
        genP R (X.map (aMap23 p q T).op σ) (Y.map (bMap23 p q T).op τ))
      = (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (eZR R)).X k) h)).hom
          (ezGen (p-1) q X Y σ τ) := by
  rw [ezGen]
  simp only [genP]
  rw [map_sum]
  simp only [map_zsmul]
  refine (Fintype.sum_equiv (shuffleEquiv p q h).symm
    (fun S : PShuffle (p-1) q => shufSign S.1 •
      ((eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (eZR R)).X k) h)).hom)
      (genP R (X.map (aHom S.1 S.2).op σ) (Y.map (bHom S.1 S.2).op τ)))
    (fun T : Sh23 p q => shufSignN T.1 •
      genP R (X.map (aMap23 p q T).op σ) (Y.map (bMap23 p q T).op τ)) ?_).symm
  intro S
  rw [ez23Map_sign p q h S, eqToHom_genP h,
    ← map_op_comp (eqToHom (congrArg SimplexCategory.mk h.symm)) (aHom S.1 S.2) σ,
    ← map_op_comp (eqToHom (congrArg SimplexCategory.mk h.symm)) (bHom S.1 S.2) τ,
    ez23Map_aHom p q h S, ez23Map_bHom p q h S]


/-! ## The `Y`-side (`Sh32` / `PShuffle p (q-1)`) reindexing -/

/-- The reindexing equivalence `PShuffle p (q-1) ≃ Sh32 p q` given by `finCongr`. -/
noncomputable def shuffleEquiv32 (p q : ℕ) (h : p+(q-1) = p+q-1) : Sh32 p q ≃ PShuffle p (q-1) where
  toFun U := ⟨(finCongr h.symm).finsetCongr U.1, by
    rw [Equiv.finsetCongr_apply, Finset.card_map]; exact U.2⟩
  invFun S := ⟨(finCongr h).finsetCongr S.1, by
    rw [Equiv.finsetCongr_apply, Finset.card_map]; exact S.2⟩
  left_inv U := by
    ext1
    show (finCongr h).finsetCongr ((finCongr h.symm).finsetCongr U.1) = U.1
    rw [Equiv.finsetCongr_apply, Equiv.finsetCongr_apply, Finset.map_map]
    ext x; simp
  right_inv S := by
    ext1
    show (finCongr h.symm).finsetCongr ((finCongr h).finsetCongr S.1) = S.1
    rw [Equiv.finsetCongr_apply, Equiv.finsetCongr_apply, Finset.map_map]
    ext x; simp

/-- The reindexing map on the `Sh32` side. -/
noncomputable abbrev ez32Map (p q : ℕ) (h : p+(q-1) = p+q-1) (S : PShuffle p (q-1)) :
    Sh32 p q :=
  (shuffleEquiv32 p q h).symm S

/-- `aMap32` is the composite of `aHom` with the `eqToHom` bridging the two bidegrees. -/
lemma ez32Map_aHom (p q : ℕ) (h : p+(q-1) = p+q-1) (S : PShuffle p (q-1)) :
    (eqToHom (congrArg SimplexCategory.mk h.symm) : ⦋p+q-1⦌ ⟶ ⦋p+(q-1)⦌) ≫ aHom S.1 S.2
      = aMap32 p q (ez32Map p q h S) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  apply Fin.ext
  show (((eqToHom (congrArg SimplexCategory.mk h.symm) : ⦋p+q-1⦌ ⟶ ⦋p+(q-1)⦌) ≫ aHom S.1 S.2) k).val
     = ((aMap32 p q (ez32Map p q h S)) k).val
  rw [comp_val, aHom_val, ← pANat_apply, eqToHom_simplex_val, pANat_eq_ANat, aMap32_apply]
  case h => exact h.symm
  exact (ANat_finsetCongr h S.1 (↑k)).symm

/-- `bMap32` is the composite of `bHom` with the `eqToHom` bridging the two bidegrees. -/
lemma ez32Map_bHom (p q : ℕ) (h : p+(q-1) = p+q-1) (S : PShuffle p (q-1)) :
    (eqToHom (congrArg SimplexCategory.mk h.symm) : ⦋p+q-1⦌ ⟶ ⦋p+(q-1)⦌) ≫ bHom S.1 S.2
      = bMap32 p q (ez32Map p q h S) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  apply Fin.ext
  show (((eqToHom (congrArg SimplexCategory.mk h.symm) : ⦋p+q-1⦌ ⟶ ⦋p+(q-1)⦌) ≫ bHom S.1 S.2) k).val
     = ((bMap32 p q (ez32Map p q h S)) k).val
  rw [comp_val, bHom_val, ← pBNat_apply, eqToHom_simplex_val, pBNat_eq_BNat, bMap32_apply]
  case h => exact h.symm
  exact (BNat_finsetCongr h S.1 (↑k)).symm

/-- `shufSignN` on the reindexed `Sh32` shuffle is `shufSign`. -/
lemma ez32Map_sign (p q : ℕ) (h : p+(q-1) = p+q-1) (S : PShuffle p (q-1)) :
    shufSign S.1 = shufSignN (ez32Map p q h S).1 := by
  rw [shufSign_eq_shufSignN, shufSignN, shufSignN]
  congr 1
  rw [show (ez32Map p q h S).1 = (finCongr h).finsetCongr S.1 from rfl]
  exact (invCountN_finsetCongr h S.1).symm

/-- **The `Sh32`-indexed shuffle chain is the `(p,q-1)` Eilenberg–Zilber shuffle chain.** -/
theorem ez32_eq_ezGen (p q : ℕ) (hq : 1 ≤ q) (X Y : SSet) (h : p+(q-1) = p+q-1)
    (σ : X _⦋p⦌) (τ : Y _⦋q-1⦌) :
    (∑ U : Sh32 p q, shufSignN U.1 •
        genP R (X.map (aMap32 p q U).op σ) (Y.map (bMap32 p q U).op τ))
      = (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (eZR R)).X k) h)).hom
          (ezGen p (q-1) X Y σ τ) := by
  rw [ezGen]
  simp only [genP]
  rw [map_sum]
  simp only [map_zsmul]
  refine (Fintype.sum_equiv (shuffleEquiv32 p q h).symm
    (fun S : PShuffle p (q-1) => shufSign S.1 •
      ((eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (eZR R)).X k) h)).hom)
      (genP R (X.map (aHom S.1 S.2).op σ) (Y.map (bHom S.1 S.2).op τ)))
    (fun U : Sh32 p q => shufSignN U.1 •
      genP R (X.map (aMap32 p q U).op σ) (Y.map (bMap32 p q U).op τ)) ?_).symm
  intro S
  rw [ez32Map_sign p q h S, eqToHom_genP h,
    ← map_op_comp (eqToHom (congrArg SimplexCategory.mk h.symm)) (aHom S.1 S.2) σ,
    ← map_op_comp (eqToHom (congrArg SimplexCategory.mk h.symm)) (bHom S.1 S.2) τ,
    ez32Map_aHom p q h S, ez32Map_bHom p q h S]


/-! ## The `rawX`/`rawY` boundary terms are the lower-bidegree shuffle chains -/

/-- The chain-level `X`-boundary term is the `(P,Q+1)`-shuffle chain, transported along the
bidegree equality `P+(Q+1) = (P+1)+(Q+1)-1`. -/
lemma rawX_eq_ezChain (P Q : ℕ) (X Y : SSet) (h : P+(Q+1) = (P+1)+(Q+1)-1)
    (w : ↥((X.chainComplex (eZR R)).X P)) (v : ↥((Y.chainComplex (eZR R)).X (Q+1))) :
    rawX P Q X Y w v = (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (eZR R)).X k) h)).hom
        (ezChain R P (Q+1) X Y w v) := by
  have hgen : ∀ (σ : X _⦋P⦌) (τ : Y _⦋Q+1⦌),
      rawX P Q X Y (genC X σ) (genC Y τ)
        = (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (eZR R)).X k) h)).hom
            (ezChain R P (Q+1) X Y (genC X σ) (genC Y τ)) := by
    intro σ τ
    rw [rawX_gen, ezChain_gen]
    exact ez23_eq_ezGen (P+1) (Q+1) (by omega) X Y h σ τ
  conv_lhs => rw [chain_eq_sum_gen X P w, chain_eq_sum_gen Y (Q+1) v]
  rw [rawX_sum_left]
  simp only [rawX_sum_right, hgen, map_sum, map_smul]
  conv_rhs => rw [chain_eq_sum_gen X P w, chain_eq_sum_gen Y (Q+1) v]
  rw [ezChain_sum_left]
  simp only [ezChain_sum_right, map_sum, map_smul]

/-- The chain-level `Y`-boundary term is the `(P+1,Q)`-shuffle chain, transported along the
bidegree equality `(P+1)+Q = (P+1)+(Q+1)-1`. -/
lemma rawY_eq_ezChain (P Q : ℕ) (X Y : SSet) (h : (P+1)+Q = (P+1)+(Q+1)-1)
    (u : ↥((X.chainComplex (eZR R)).X (P+1))) (w : ↥((Y.chainComplex (eZR R)).X Q)) :
    rawY P Q X Y u w = (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (eZR R)).X k) h)).hom
        (ezChain R (P+1) Q X Y u w) := by
  have hgen : ∀ (σ : X _⦋P+1⦌) (τ : Y _⦋Q⦌),
      rawY P Q X Y (genC X σ) (genC Y τ)
        = (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (eZR R)).X k) h)).hom
            (ezChain R (P+1) Q X Y (genC X σ) (genC Y τ)) := by
    intro σ τ
    rw [rawY_gen, ezChain_gen]
    exact ez32_eq_ezGen (P+1) (Q+1) (by omega) X Y h σ τ
  conv_lhs => rw [chain_eq_sum_gen X (P+1) u, chain_eq_sum_gen Y Q w]
  rw [rawY_sum_left]
  simp only [rawY_sum_right, hgen, map_sum, map_smul]
  conv_rhs => rw [chain_eq_sum_gen X (P+1) u, chain_eq_sum_gen Y Q w]
  rw [ezChain_sum_left]
  simp only [ezChain_sum_right, map_sum, map_smul]


/-! ## The degenerate shuffles -/

/-- The unique `(0,q)`-shuffle. -/
def zSh (q : ℕ) : PShuffle 0 q := ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin, Nat.zero_add]⟩

lemma zSh_eq (q : ℕ) (S : PShuffle 0 q) : S = zSh q := by
  apply Subtype.ext
  apply Finset.eq_univ_of_card
  rw [S.2, Fintype.card_fin, Nat.zero_add]

lemma zSh_shufSign (q : ℕ) : shufSign (zSh q).1 = 1 := by
  rw [shufSign, invCount]
  simp [zSh]

/-- The unique `(p,0)`-shuffle. -/
def zSh0 (p : ℕ) : PShuffle p 0 := ⟨∅, by simp⟩

lemma zSh0_eq (p : ℕ) (S : PShuffle p 0) : S = zSh0 p := by
  apply Subtype.ext
  simpa [zSh0] using (Finset.card_eq_zero.mp S.2)

lemma zSh0_shufSign (p : ℕ) : shufSign (zSh0 p).1 = 1 := by
  rw [shufSign, invCount]
  simp [zSh0, pBNat]

/-- Two morphisms into `⦋0⦌` from the same source are equal. -/
lemma hom_zero_unique {m : ℕ} (f g : ⦋m⦌ ⟶ ⦋0⦌) : f = g := by
  rw [SimplexCategory.eq_const_to_zero f, SimplexCategory.eq_const_to_zero g]

/-- The `(0,q)`-shuffle chain is a single `genP R` (the shuffle `(0,q)` is unique). -/
lemma ezGen_zero_single (q : ℕ) (X Y : SSet) (σ : X _⦋0⦌) (τ : Y _⦋q⦌) :
    ezGen 0 q X Y σ τ
      = genP R (X.map (aHom (zSh q).1 (zSh q).2).op σ)
             (Y.map (bHom (zSh q).1 (zSh q).2).op τ) := by
  rw [ezGen, Finset.sum_eq_single_of_mem (zSh q) (Finset.mem_univ _)
    (fun S _ hS => absurd (zSh_eq q S) hS)]
  rw [zSh_shufSign, one_smul]
  rfl

/-- The `(p,0)`-shuffle chain is a single `genP R` (the shuffle `(p,0)` is unique). -/
lemma ezGen_zero_single_right (p : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋0⦌) :
    ezGen p 0 X Y σ τ
      = genP R (X.map (aHom (zSh0 p).1 (zSh0 p).2).op σ)
             (Y.map (bHom (zSh0 p).1 (zSh0 p).2).op τ) := by
  rw [ezGen, Finset.sum_eq_single_of_mem (zSh0 p) (Finset.mem_univ _)
    (fun S _ hS => absurd (zSh0_eq p S) hS)]
  rw [zSh0_shufSign, one_smul]
  rfl


/-- The `bHom` of the unique `(0,q)`-shuffle preserves the vertex value. -/
lemma bHom_val_eq (q : ℕ) (i : Fin (0+q+1)) :
    (((bHom (p := 0) (q := q) (zSh q).1 (zSh q).2) : ⦋0+q⦌ ⟶ ⦋q⦌) i).val = i.val := by
  rw [show (((bHom (p := 0) (q := q) (zSh q).1 (zSh q).2) : ⦋0+q⦌ ⟶ ⦋q⦌) i).val
      = pB (zSh q).1 i from bHom_val _ _ _]
  rw [show (zSh q).1 = (Finset.univ : Finset (Fin (0+q))) from rfl, pB,
    card_univ_filter_val_lt, Nat.min_eq_left (by omega : (i : ℕ) ≤ 0+q)]

/-- `δ j ≫ aHom` of the unique `(0,Q+1)`-shuffle is the `aHom` of the unique `(0,Q)`-shuffle. -/
lemma zSh_aHom_compat (Q : ℕ) (j : Fin ((0+Q)+2)) :
    SimplexCategory.δ j ≫ aHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2
      = aHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2 := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  apply Fin.ext
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  show ((aHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2 : ⦋0+(Q+1)⦌ ⟶ ⦋0⦌)
      (SimplexCategory.δ j k)).val
    = ((aHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2 : ⦋0+Q⦌ ⟶ ⦋0⦌) k).val
  rw [aHom_val, aHom_val]
  simp only [pA, zSh]
  rw [Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _),
    Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)]
  simp

/-- `bHom` is compatible with the face maps (the `(0,Q+1)`- and `(0,Q)`-shuffles). -/
lemma zSh_bHom_compat (Q : ℕ) (j : Fin ((0+Q)+2)) :
    SimplexCategory.δ j ≫ bHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2
      = bHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2
          ≫ SimplexCategory.δ (finCongr (by omega : (0+Q)+2 = Q+2) j) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  apply Fin.ext
  rw [SimplexCategory.comp_toOrderHom, SimplexCategory.comp_toOrderHom,
    OrderHom.comp_coe, OrderHom.comp_coe, Function.comp_apply, Function.comp_apply]
  show ((bHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2 : ⦋0+(Q+1)⦌ ⟶ ⦋Q+1⦌)
      (SimplexCategory.δ j k)).val
    = ((SimplexCategory.δ (finCongr (by omega : (0+Q)+2 = Q+2) j))
        ((bHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2 : ⦋0+Q⦌ ⟶ ⦋Q⦌) k)).val
  rw [show (((bHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2) : ⦋0+(Q+1)⦌ ⟶ ⦋Q+1⦌)
      (SimplexCategory.δ j k)).val = (SimplexCategory.δ j k).val from bHom_val_eq (Q+1) _]
  rw [show ((SimplexCategory.δ j) k).val = delV j.val k.val from delta_val j k]
  rw [show ((SimplexCategory.δ (finCongr (by omega : (0+Q)+2 = Q+2) j))
      ((bHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2) k)).val
      = delV (finCongr (by omega : (0+Q)+2 = Q+2) j).val
          (((bHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2) k) : ℕ)
      from delta_val _ _]
  rw [show (((bHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2) : ⦋0+Q⦌ ⟶ ⦋Q⦌) k).val = k.val
      from bHom_val_eq Q _]
  rw [finCongr_val]


/-- The degenerate `(0,Q+1)` case of the derivation identity. -/
lemma ezChain_d_left0 (Q : ℕ) (X Y : SSet)
    (u : ↥((X.chainComplex (eZR R)).X 0)) (v : ↥((Y.chainComplex (eZR R)).X (Q+1))) :
    (((X ⊗ Y).chainComplex (eZR R)).d (0+(Q+1)) (0+Q)).hom (ezChain R 0 (Q+1) X Y u v)
      = ezChain R 0 Q X Y u (((Y.chainComplex (eZR R)).d (Q+1) Q).hom v) := by
  have key : ∀ (σ : X _⦋0⦌) (τ : Y _⦋Q+1⦌),
      (((X ⊗ Y).chainComplex (eZR R)).d (0+(Q+1)) (0+Q)).hom
          (ezChain R 0 (Q+1) X Y (genC X σ) (genC Y τ))
        = ezChain R 0 Q X Y (genC X σ) (((Y.chainComplex (eZR R)).d (Q+1) Q).hom (genC Y τ)) := by
    intro σ τ
    rw [ezChain_gen, ezGen_zero_single]
    change ((X ⊗ Y).chainComplex (eZR R)).d ((0+Q)+1) (0+Q)
        (genP R (X.map (aHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2).op σ)
          (Y.map (bHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2).op τ)) = _
    rw [d_genP R (n := 0+Q)]
    rw [d_genC Q Y τ]
    rw [ezChain_sum_right_zsmul]
    simp only [ezChain_gen, ezGen_zero_single]
    have hterm : ∀ j : Fin ((0+Q)+2),
        ((-1 : ℤ) ^ (j : ℕ)) • genP R
            (X.δ j (X.map (aHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2).op σ))
            (Y.δ j (Y.map (bHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2).op τ))
          = ((-1 : ℤ) ^ (((finCongr (by omega : (0+Q)+2 = Q+2)) j) : ℕ)) • genP R
              (X.map (aHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2).op σ)
              (Y.map (bHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2).op
                (Y.δ ((finCongr (by omega : (0+Q)+2 = Q+2)) j) τ)) := by
      intro j
      rw [show (((finCongr (by omega : (0+Q)+2 = Q+2)) j) : ℕ) = (j : ℕ) from finCongr_val _ _]
      congr 1
      rw [map_delta, zSh_aHom_compat, map_delta, zSh_bHom_compat, map_op_comp]
      rfl
    rw [Fintype.sum_equiv (finCongr (by omega : (0+Q)+2 = Q+2))
      (fun j : Fin ((0+Q)+2) => ((-1 : ℤ) ^ (j : ℕ)) • genP R
          (X.δ j (X.map (aHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2).op σ))
          (Y.δ j (Y.map (bHom (p := 0) (q := Q+1) (zSh (Q+1)).1 (zSh (Q+1)).2).op τ)))
      (fun j' : Fin (Q+2) => ((-1 : ℤ) ^ (j' : ℕ)) • genP R
          (X.map (aHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2).op σ)
          (Y.map (bHom (p := 0) (q := Q) (zSh Q).1 (zSh Q).2).op (Y.δ j' τ)))
      hterm]
  conv_lhs => rw [chain_eq_sum_gen X 0 u, chain_eq_sum_gen Y (Q+1) v]
  rw [ezChain_sum_left]
  simp only [ezChain_sum_right, map_sum, map_smul]
  have hdv : ((Y.chainComplex (eZR R)).d (Q+1) Q).hom v
      = ∑ τ ∈ (coords Y (Q+1) v).support,
          (coords Y (Q+1) v) τ • (((Y.chainComplex (eZR R)).d (Q+1) Q).hom (genC Y τ)) := by
    conv_lhs => rw [chain_eq_sum_gen Y (Q+1) v]
    rw [map_sum]
    simp only [map_smul]
  rw [hdv]
  conv_rhs => rw [chain_eq_sum_gen X 0 u]
  rw [ezChain_sum_left]
  simp only [ezChain_sum_right, map_sum, map_smul]
  apply Finset.sum_congr rfl; intro σ _
  congr 1
  apply Finset.sum_congr rfl; intro τ _
  rw [key σ τ]


/-- The `aHom` of the unique `(P,0)`-shuffle preserves the vertex value. -/
lemma aHom_zSh0_val (P : ℕ) (i : Fin (P+0+1)) :
    (((aHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2) : ⦋P+0⦌ ⟶ ⦋P⦌) i).val = i.val := by
  rw [show (((aHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2) : ⦋P+0⦌ ⟶ ⦋P⦌) i).val
      = pA (zSh0 P).1 i from aHom_val _ _ _]
  rw [show (zSh0 P).1 = (∅ : Finset (Fin (P+0))) from rfl, pA, Finset.sdiff_empty,
    card_univ_filter_val_lt, Nat.min_eq_left (by omega : (i : ℕ) ≤ P+0)]

/-- The `aHom` compatibility for the `(P,0)`-shuffles. -/
lemma zSh0_aHom_compat (P : ℕ) (i : Fin (P+2)) :
    SimplexCategory.δ i ≫ aHom (p := P+1) (q := 0) (zSh0 (P+1)).1 (zSh0 (P+1)).2
      = aHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2 ≫ SimplexCategory.δ i := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  apply Fin.ext
  rw [SimplexCategory.comp_toOrderHom, SimplexCategory.comp_toOrderHom,
    OrderHom.comp_coe, OrderHom.comp_coe, Function.comp_apply, Function.comp_apply]
  show ((aHom (p := P+1) (q := 0) (zSh0 (P+1)).1 (zSh0 (P+1)).2 : ⦋(P+1)+0⦌ ⟶ ⦋P+1⦌)
      (SimplexCategory.δ i k)).val
    = ((SimplexCategory.δ i)
        ((aHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2 : ⦋P+0⦌ ⟶ ⦋P⦌) k)).val
  rw [show (((aHom (p := P+1) (q := 0) (zSh0 (P+1)).1 (zSh0 (P+1)).2) : ⦋(P+1)+0⦌ ⟶ ⦋P+1⦌)
      (SimplexCategory.δ i k)).val = (SimplexCategory.δ i k).val from aHom_zSh0_val (P+1) _]
  rw [show ((SimplexCategory.δ i) k).val = delV i.val k.val from delta_val i k]
  rw [show ((SimplexCategory.δ i) ((aHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2) k)).val
      = delV i.val (((aHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2) k) : ℕ) from delta_val i _]
  rw [show (((aHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2) : ⦋P+0⦌ ⟶ ⦋P⦌) k).val = k.val
      from aHom_zSh0_val P _]

/-- The `bHom` compatibility for the `(P,0)`-shuffles. -/
lemma zSh0_bHom_compat (P : ℕ) (i : Fin (P+2)) :
    SimplexCategory.δ i ≫ bHom (p := P+1) (q := 0) (zSh0 (P+1)).1 (zSh0 (P+1)).2
      = bHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2 := by
  rw [SimplexCategory.eq_const_to_zero
      (SimplexCategory.δ i ≫ bHom (p := P+1) (q := 0) (zSh0 (P+1)).1 (zSh0 (P+1)).2),
    SimplexCategory.eq_const_to_zero (bHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2)]
  rfl

/-- The degenerate `(P+1,0)` case of the derivation identity. -/
lemma ezChain_d_right0 (P : ℕ) (X Y : SSet)
    (u : ↥((X.chainComplex (eZR R)).X (P+1))) (v : ↥((Y.chainComplex (eZR R)).X 0)) :
    (((X ⊗ Y).chainComplex (eZR R)).d (P+1) P).hom (ezChain R (P+1) 0 X Y u v)
      = ezChain R P 0 X Y (((X.chainComplex (eZR R)).d (P+1) P).hom u) v := by
  have key : ∀ (σ : X _⦋P+1⦌) (τ : Y _⦋0⦌),
      (((X ⊗ Y).chainComplex (eZR R)).d (P+1) P).hom
          (ezChain R (P+1) 0 X Y (genC X σ) (genC Y τ))
        = ezChain R P 0 X Y (((X.chainComplex (eZR R)).d (P+1) P).hom (genC X σ)) (genC Y τ) := by
    intro σ τ
    rw [ezChain_gen, ezGen_zero_single_right]
    rw [d_genP R (n := P)]
    rw [d_genC P X σ]
    rw [ezChain_sum_left_zsmul]
    simp only [ezChain_gen, ezGen_zero_single_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    apply congrArg₂ (genP R)
    · rw [map_delta,
        show ((SimplicialObject.δ X i) σ) = X.map (SimplexCategory.δ i).op σ from rfl,
        ← map_op_comp (aHom (p := P) (q := 0) (zSh0 P).1 (zSh0 P).2)
          (SimplexCategory.δ i) σ, zSh0_aHom_compat]
    · rw [map_delta, zSh0_bHom_compat]
  have hdu : ((X.chainComplex (eZR R)).d (P+1) P).hom u
      = ∑ σ ∈ (coords X (P+1) u).support,
          (coords X (P+1) u) σ • (((X.chainComplex (eZR R)).d (P+1) P).hom (genC X σ)) := by
    conv_lhs => rw [chain_eq_sum_gen X (P+1) u]
    rw [map_sum]
    simp only [map_smul]
  rw [hdu]
  conv_rhs => rw [chain_eq_sum_gen Y 0 v]
  rw [ezChain_sum_left]
  simp only [ezChain_sum_right, ezChain_gen, ezGen_zero_single_right]
  conv_lhs => rw [chain_eq_sum_gen X (P+1) u, chain_eq_sum_gen Y 0 v]
  rw [ezChain_sum_left]
  simp only [ezChain_sum_right, map_sum, map_smul]
  apply Finset.sum_congr rfl; intro σ _
  congr 1
  apply Finset.sum_congr rfl; intro τ _
  rw [key σ τ]

end

end Work.SSSR.KunnethEZ





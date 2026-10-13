/-
  Area E7 (Binyamini–Vorobjov §§3–4): vocabulary.

  Everything here is *new* notation built on the frozen area-E vocabulary in
  `Submission.Work.Wilkies.E.Spec` (namespace `WilkiesDesign.E`).

  The two operations that BV's argument needs beyond the frozen vocabulary are

  * `SemiPf.pad`  : view a semi-Pfaffian set in `ℝ^k` as one in `ℝ^K`, `k ≤ K`
                    (zero-padding the extra coordinates of the chain);
  * `SemiPf.reindex` : rename the coordinates along an equivalence `Fin k ≃ Fin K`
                    (used to move between `SemiPf ((n+1)+m)` and `SemiPf (n+(m+1))`),

  together with the "chain concatenation" `SemiPf.unionSet` that expresses a union of
  two semi-Pfaffian sets in the same ambient space (the chains are merged, so the
  format grows -- that is why `Star` keeps a list of pieces instead of one `SemiPf`).
-/
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Compatibility of a finite family with a set -/

/-- A finite family of sets is *compatible* with `Y` if every member is either contained
in `Y` or disjoint from `Y` (BV: "compatible with"). -/
def Compatible {n : ℕ} (C : Finset (Set (Fin n → ℝ))) (Y : Set (Fin n → ℝ)) : Prop :=
  ∀ κ ∈ C, κ ⊆ Y ∨ Disjoint κ Y

/-! ## Truncating and zero-padding coordinates -/

/-- Truncate `x : Fin K → ℝ` to its first `k ≤ K` coordinates. -/
def takeZ {k K : ℕ} (hm : k ≤ K) (x : Fin K → ℝ) : Fin k → ℝ :=
  fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hm⟩

/-- Pad `x : Fin k → ℝ` with zeros to `K` coordinates. -/
def padZ (K : ℕ) {k : ℕ} (x : Fin k → ℝ) : Fin K → ℝ :=
  fun i => if h : i.val < k then x ⟨i.val, h⟩ else 0

/-! ## Padding (lifting) a chain and a semi-Pfaffian set to more variables -/

/-- Pad a chain to `K ≥ k` variables: the extra coefficients are zero. -/
def EAChain.pad {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) : EAChain K r :=
  ⟨fun j i => if h : i.val < k then c.a j ⟨i.val, h⟩ else 0, c.b⟩

/-- Pad an `EA`-polynomial to `K ≥ k` coordinates (no variables are added). -/
def EAPoly.pad {k K r : ℕ} (hm : k ≤ K) (Q : EAPoly k r) : EAPoly K r :=
  MvPolynomial.rename (Sum.map (Fin.castLE hm) id) Q

/-- Pad a basic set to `K ≥ k` coordinates. -/
def Basic.pad {k K r : ℕ} (hm : k ≤ K) (B : Basic k r) : Basic K r :=
  ⟨B.eqs.map (EAPoly.pad hm), B.pos.map (EAPoly.pad hm)⟩

/-- View a semi-Pfaffian set in `ℝ^k` as one in `ℝ^K`, `k ≤ K`. -/
def SemiPf.pad {k K : ℕ} (hm : k ≤ K) (X : SemiPf k) : SemiPf K :=
  ⟨X.r, EAChain.pad hm X.c, X.basics.map (Basic.pad hm)⟩

/-! ## Concatenating two chains (union in a fixed ambient space) -/

/-- Concatenate two chains over the same coordinates. -/
def EAChain.cat {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂) :
    EAChain k (r₁ + r₂) :=
  ⟨fun j i => Fin.addCases (fun j₁ => c₁.a j₁ i) (fun j₂ => c₂.a j₂ i) j,
   fun j => Fin.addCases (fun j₁ => c₁.b j₁) (fun j₂ => c₂.b j₂) j⟩

/-- Reindex an `EA`-polynomial of a `r₁`-chain as a polynomial of the concatenation. -/
def EAPoly.inl {k r₁ r₂ : ℕ} (Q : EAPoly k r₁) : EAPoly k (r₁ + r₂) :=
  MvPolynomial.rename (Sum.map id (Fin.castAdd r₂)) Q

/-- Reindex an `EA`-polynomial of a `r₂`-chain as a polynomial of the concatenation. -/
def EAPoly.inr {k r₁ r₂ : ℕ} (Q : EAPoly k r₂) : EAPoly k (r₁ + r₂) :=
  MvPolynomial.rename (Sum.map id (Fin.natAdd r₁)) Q

/-- Reindex a basic set for the concatenated chain. -/
def Basic.inl {k r₁ r₂ : ℕ} (B : Basic k r₁) : Basic k (r₁ + r₂) :=
  ⟨B.eqs.map EAPoly.inl, B.pos.map EAPoly.inl⟩

/-- Reindex a basic set for the concatenated chain. -/
def Basic.inr {k r₁ r₂ : ℕ} (B : Basic k r₂) : Basic k (r₁ + r₂) :=
  ⟨B.eqs.map EAPoly.inr, B.pos.map EAPoly.inr⟩

/-- The union of two semi-Pfaffian sets in the same ambient space: the chains are
concatenated and the two DNF lists appended. -/
def SemiPf.unionSet {k : ℕ} (X Y : SemiPf k) : SemiPf k :=
  ⟨X.r + Y.r, EAChain.cat X.c Y.c,
   (X.basics.map Basic.inl) ++ (Y.basics.map Basic.inr)⟩

/-! ## Reindexing coordinates along an equivalence -/

/-- The value-preserving equivalence `Fin K ≃ Fin K'` induced by `K = K'`. -/
def finEquiv {K K' : ℕ} (h : K = K') : Fin K ≃ Fin K' where
  toFun i := ⟨i.val, h ▸ i.isLt⟩
  invFun j := ⟨j.val, h.symm ▸ j.isLt⟩
  left_inv i := Fin.ext rfl
  right_inv j := Fin.ext rfl

@[simp] theorem finEquiv_apply_val {K K' : ℕ} (h : K = K') (i : Fin K) :
    ((finEquiv h) i).val = i.val := rfl

/-- Reindex a chain along an equivalence of coordinate sets. -/
def EAChain.reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r) : EAChain K r :=
  ⟨fun j i => c.a j (e.symm i), c.b⟩

/-- Reindex an `EA`-polynomial along an equivalence of coordinate sets. -/
def EAPoly.reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (Q : EAPoly k r) : EAPoly K r :=
  MvPolynomial.rename (Sum.map e id) Q

/-- Reindex a basic set along an equivalence of coordinate sets. -/
def Basic.reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (B : Basic k r) : Basic K r :=
  ⟨B.eqs.map (EAPoly.reindex e), B.pos.map (EAPoly.reindex e)⟩

/-- Reindex a semi-Pfaffian set along an equivalence of coordinate sets. -/
def SemiPf.reindex {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) : SemiPf K :=
  ⟨X.r, EAChain.reindex e X.c, X.basics.map (Basic.reindex e)⟩

/-! ## The projection of a `*`-piece -/

/-- The `*`-piece obtained from `P : StarPiece (N+1)` by dropping the last coordinate:
the semi-Pfaffian set is reindexed along the (value preserving) identification
`(N+1)+m = N+(m+1)`, and the new fibre dimension is `m+1`. -/
def StarPiece.init {N : ℕ} (P : StarPiece (N + 1)) : StarPiece N :=
  ⟨P.m + 1, SemiPf.reindex (finEquiv (by omega : (N + 1) + P.m = N + (P.m + 1))) P.X,
   fun i => P.p ((finEquiv (by omega : (N + 1) + P.m = N + (P.m + 1))).symm i)⟩

/-- Format of a `*`-piece. -/
def StarPiece.fmt {n : ℕ} (P : StarPiece n) : ℕ := P.X.fmt

/-- Degree of a `*`-piece. -/
def StarPiece.deg {n : ℕ} (P : StarPiece n) : ℕ := P.X.deg

/-! ## Selections of cells of a decomposition -/

/-- The cells of `C` lying outside `Y`.  The `DecidablePred` instance is pinned to
`Classical.propDecidable`, so that uses of this definition never depend on instance
synthesis (which would otherwise pick different, merely propositionally equal,
instances in different files). -/
def cellsOutside {n : ℕ} (C : Finset (Set (Fin n → ℝ))) (Y : Set (Fin n → ℝ)) :
    Finset (Set (Fin n → ℝ)) :=
  @Finset.filter (Set (Fin n → ℝ)) (fun κ => Disjoint κ Y)
    (fun a => Classical.propDecidable (Disjoint a Y)) C

/-- The cells of `C` lying inside every `Y i` (instance pinned as in `cellsOutside`). -/
def cellsInside {n : ℕ} {ι : Type*} (C : Finset (Set (Fin n → ℝ))) (Y : ι → Set (Fin n → ℝ)) :
    Finset (Set (Fin n → ℝ)) :=
  @Finset.filter (Set (Fin n → ℝ)) (fun κ => ∀ i, κ ⊆ Y i)
    (fun a => Classical.propDecidable (∀ i, a ⊆ Y i)) C

/-- The `M`-fold coordinate projection of a decomposition of `ℝ^{n+M}`. -/
def cylImage (n : ℕ) : (M : ℕ) → Finset (Set (Fin (n + M) → ℝ)) → Finset (Set (Fin n → ℝ))
  | 0, C => C
  | M + 1, C => cylImage n M (C.image (fun c => projFirst (n + M) 1 '' c))

@[simp] theorem cylImage_zero {n : ℕ} (C : Finset (Set (Fin (n + 0) → ℝ))) :
    cylImage n 0 C = C := rfl

/-! ## API for the selections

These are stated with the instance passed explicitly, so that they never trigger
type-class synthesis (which would otherwise insert a different, only propositionally
equal, `DecidablePred` instance than the one pinned in `cellsOutside`/`cellsInside`). -/

theorem mem_cellsOutside {n : ℕ} {C : Finset (Set (Fin n → ℝ))} {Z : Set (Fin n → ℝ)}
    {κ : Set (Fin n → ℝ)} : κ ∈ cellsOutside C Z ↔ κ ∈ C ∧ Disjoint κ Z :=
  @Finset.mem_filter (Set (Fin n → ℝ)) (fun κ => Disjoint κ Z)
    (fun a => Classical.propDecidable (Disjoint a Z)) C κ

theorem mem_cellsInside {n : ℕ} {ι : Type*} {C : Finset (Set (Fin n → ℝ))}
    {Y : ι → Set (Fin n → ℝ)} {κ : Set (Fin n → ℝ)} :
    κ ∈ cellsInside C Y ↔ κ ∈ C ∧ ∀ i, κ ⊆ Y i :=
  @Finset.mem_filter (Set (Fin n → ℝ)) (fun κ => ∀ i, κ ⊆ Y i)
    (fun a => Classical.propDecidable (∀ i, a ⊆ Y i)) C κ

theorem card_cellsOutside_le {n : ℕ} (C : Finset (Set (Fin n → ℝ))) (Z : Set (Fin n → ℝ)) :
    (cellsOutside C Z).card ≤ C.card :=
  @Finset.card_filter_le (Set (Fin n → ℝ)) C (fun κ => Disjoint κ Z)
    (fun a => Classical.propDecidable (Disjoint a Z))

theorem card_cellsInside_le {n : ℕ} {ι : Type*} (C : Finset (Set (Fin n → ℝ)))
    (Y : ι → Set (Fin n → ℝ)) : (cellsInside C Y).card ≤ C.card :=
  @Finset.card_filter_le (Set (Fin n → ℝ)) C (fun κ => ∀ i, κ ⊆ Y i)
    (fun a => Classical.propDecidable (∀ i, a ⊆ Y i))

end Work.WilE7

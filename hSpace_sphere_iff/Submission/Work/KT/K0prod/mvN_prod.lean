import Mathlib
import Submission.Work.KT.K0_prod_defs

/-!
# Murray–von Neumann equivalence over a product ring

`Mat.MvN` is defined for matrices over a ring `R` (`Submission/Work/KT/Defs.lean`).  The matrix
ring over a product ring `A × B` is the product of the matrix rings over `A` and over `B`:
entrywise, the two projections `A × B → A`, `A × B → B` commute with sums and products.  Hence a
pair of matrices over `A × B` is Murray–von Neumann equivalent as soon as its two images are.

This is the ingredient of `K₀(R × S) ≅ K₀(R) × K₀(S)` (`Work.KT.K0_prod`) that says the
"pairing" map `K₀(A × B) → K₀(A) × K₀(B)` is *injective on the level of matrices*: the witnesses
of `Mat.MvN` over `A` and over `B` assemble, entrywise, into a witness over `A × B`.

The auxiliary `prodMk`-lemmas are stated for general index types so that the (syntactically
distinct but definitionally equal) index types `Fin (p.map φ).1` and `Fin p.1` cause no trouble:
`mvN_prod_aux` uses the *same* index type for the two matrices of a pair.
-/

namespace Work.KT.K0prod

variable {A B : Type} [Ring A] [Ring B]

/-- The matrix over `A × B` whose two projections are `M` and `N`. -/
def prodMk {m n : Type} (M : Matrix m n A) (N : Matrix m n B) : Matrix m n (A × B) :=
  fun i j => (M i j, N i j)

@[simp] lemma map_fst_prodMk {m n : Type} (M : Matrix m n A) (N : Matrix m n B) :
    Matrix.map (prodMk M N) (RingHom.fst A B) = M := by ext i j; rfl

@[simp] lemma map_snd_prodMk {m n : Type} (M : Matrix m n A) (N : Matrix m n B) :
    Matrix.map (prodMk M N) (RingHom.snd A B) = N := by ext i j; rfl

/-- `prodMk` is multiplicative. -/
lemma prodMk_mul {m n o : Type} [Fintype n] (M : Matrix m n A) (M' : Matrix n o A)
    (N : Matrix m n B) (N' : Matrix n o B) :
    prodMk (M * M') (N * N') = prodMk M N * prodMk M' N' := by
  ext i j
  · simp only [prodMk, Matrix.mul_apply, Prod.fst_sum, Prod.fst_mul]
  · simp only [prodMk, Matrix.mul_apply, Prod.snd_sum, Prod.snd_mul]

/-- Every matrix over `A × B` is the `prodMk` of its two projections. -/
lemma prodMk_map {m n : Type} (M : Matrix m n (A × B)) :
    prodMk (Matrix.map M (RingHom.fst A B)) (Matrix.map M (RingHom.snd A B)) = M := by
  refine Matrix.ext (fun i j => Prod.ext ?_ ?_)
  · rfl
  · rfl

/-- The two projections of a matrix over `A × B` determine it. -/
lemma eq_iff_map_prod {m n : Type} (M N : Matrix m n (A × B)) :
    M = N ↔ Matrix.map M (RingHom.fst A B) = Matrix.map N (RingHom.fst A B) ∧
      Matrix.map M (RingHom.snd A B) = Matrix.map N (RingHom.snd A B) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    refine Matrix.ext (fun i j => Prod.ext ?_ ?_)
    · exact congrFun (congrFun h1 i) j
    · exact congrFun (congrFun h2 i) j

/-- Murray–von Neumann equivalence is detected componentwise: `mvN_prod_aux` proves the
statement for square matrices whose index types are *literally* the same, so that the
`prodMk`-rewrites apply syntactically. -/
lemma mvN_prod_aux {m n : ℕ} (P : Matrix (Fin m) (Fin m) (A × B))
    (Q : Matrix (Fin n) (Fin n) (A × B))
    (hA : ∃ (a : Matrix (Fin n) (Fin m) A) (b : Matrix (Fin m) (Fin n) A),
      b * a = Matrix.map P (RingHom.fst A B) ∧ a * b = Matrix.map Q (RingHom.fst A B))
    (hB : ∃ (a : Matrix (Fin n) (Fin m) B) (b : Matrix (Fin m) (Fin n) B),
      b * a = Matrix.map P (RingHom.snd A B) ∧ a * b = Matrix.map Q (RingHom.snd A B)) :
    ∃ (a : Matrix (Fin n) (Fin m) (A × B)) (b : Matrix (Fin m) (Fin n) (A × B)),
      b * a = P ∧ a * b = Q := by
  obtain ⟨aA, bA, hbaA, habA⟩ := hA
  obtain ⟨aB, bB, hbaB, habB⟩ := hB
  exact ⟨prodMk aA aB, prodMk bA bB,
    by rw [← prodMk_mul, hbaA, hbaB]; exact prodMk_map P,
    by rw [← prodMk_mul, habA, habB]; exact prodMk_map Q⟩

lemma mvN_prod {A B : Type} [Ring A] [Ring B] (p q : Mat (A × B))
    (hA : Mat.MvN (p.map (RingHom.fst A B)) (q.map (RingHom.fst A B)))
    (hB : Mat.MvN (p.map (RingHom.snd A B)) (q.map (RingHom.snd A B))) :
    Mat.MvN p q := by
  obtain ⟨m, P⟩ := p
  obtain ⟨n, Q⟩ := q
  have hA' : ∃ (a : Matrix (Fin n) (Fin m) A) (b : Matrix (Fin m) (Fin n) A),
      b * a = Matrix.map P (RingHom.fst A B) ∧ a * b = Matrix.map Q (RingHom.fst A B) := hA
  have hB' : ∃ (a : Matrix (Fin n) (Fin m) B) (b : Matrix (Fin m) (Fin n) B),
      b * a = Matrix.map P (RingHom.snd A B) ∧ a * b = Matrix.map Q (RingHom.snd A B) := hB
  exact mvN_prod_aux P Q hA' hB'

end Work.KT.K0prod

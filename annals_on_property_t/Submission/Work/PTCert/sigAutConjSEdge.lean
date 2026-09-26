import Mathlib
import Submission.Work.PTCert.Interfaces
import Submission.Work.RouteB.EdgeLap
import Submission.Work.PTCert.sigmaGroupFacts

/-!
# Conjugation of the edge transvection sets by signed permutations

The signed permutations `sigAut p s = signAut s * permAut p` of `Σ_r ≤ Aut(F_r)`
act by conjugation on the edge transvection sets `SEdge e` of the standard
simplex, and permute the edges: `MulAut.conj (sigAut p s) '' SEdge e = SEdge (p • e)`.

The proof decomposes the conjugation:
* `permAut p` alone moves the edge `e` to `p • e` (`SEdge_image_conj`, from
  `RouteB/EdgeLap.lean`);
* a sign flip `signAut s` (a product of single-generator inversions `sigma i`)
  preserves every `SEdge e` setwise, because conjugating a Nielsen transvection
  of `(u,v)` by `sigma i` produces another transvection of the same unordered
  pair `{u,v}` (`sigma_conj_dirEdge_mem`).
-/

namespace Work.PTCert

open Submission.PTCert Submission.RouteB Submission.RouteB.Edge Submission.FreeGroupAut

/-! ## Conjugation by a single-generator inversion preserves the edge transvections -/

/-- Conjugating a transvection of the ordered pair `(u,v)` by `sigma i` produces a
transvection of the same ordered pair: `σ` exchanges `ρ ↔ λ` and flips the sign
according to whether `i` is the first or the second index, and fixes it otherwise. -/
lemma sigma_conj_dirEdge_mem {m : ℕ} {i u v : Fin m} (huv : u ≠ v)
    {g : MulAut (FreeGroup (Fin m))} (hg : g ∈ dirEdge u v huv) :
    sigma i * g * sigma i ∈ dirEdge u v huv := by
  rw [mem_dirEdge] at hg ⊢
  rcases hg with h | h | h | h <;> subst h
  · by_cases hiu : i = u
    · rw [hiu]
      have hx : sigma u * rho u v huv * sigma u = lamNeg u v huv :=
        Commons.GroupTheory.FreeGroup.sigma_conj_rho_left u v huv
      rw [hx]; exact Or.inr (Or.inr (Or.inr rfl))
    · by_cases hiv : i = v
      · rw [hiv]
        have hx : sigma v * rho u v huv * sigma v = rhoNeg u v huv :=
          Commons.GroupTheory.FreeGroup.sigma_conj_rho_right u v huv
        rw [hx]; exact Or.inr (Or.inl rfl)
      · have hx : sigma i * rho u v huv * sigma i = rho u v huv :=
          Commons.GroupTheory.FreeGroup.sigma_conj_rho_neither i u v huv hiu hiv
        rw [hx]; exact Or.inl rfl
  · by_cases hiu : i = u
    · rw [hiu]
      have hx : sigma u * rhoNeg u v huv * sigma u = lam u v huv :=
        Commons.GroupTheory.FreeGroup.sigma_conj_rhoNeg_left u v huv
      rw [hx]; exact Or.inr (Or.inr (Or.inl rfl))
    · by_cases hiv : i = v
      · rw [hiv]
        have hx : sigma v * rhoNeg u v huv * sigma v = rho u v huv :=
          Commons.GroupTheory.FreeGroup.sigma_conj_rhoNeg_right u v huv
        rw [hx]; exact Or.inl rfl
      · have hx : sigma i * rhoNeg u v huv * sigma i = rhoNeg u v huv :=
          Commons.GroupTheory.FreeGroup.sigma_conj_rhoNeg_neither i u v huv hiu hiv
        rw [hx]; exact Or.inr (Or.inl rfl)
  · by_cases hiu : i = u
    · rw [hiu]
      have hx : sigma u * lam u v huv * sigma u = rhoNeg u v huv :=
        Commons.GroupTheory.FreeGroup.sigma_conj_lam_left u v huv
      rw [hx]; exact Or.inr (Or.inl rfl)
    · by_cases hiv : i = v
      · rw [hiv]
        have hx : sigma v * lam u v huv * sigma v = lamNeg u v huv :=
          Commons.GroupTheory.FreeGroup.sigma_conj_lam_right u v huv
        rw [hx]; exact Or.inr (Or.inr (Or.inr rfl))
      · have hx : sigma i * lam u v huv * sigma i = lam u v huv :=
          Commons.GroupTheory.FreeGroup.sigma_conj_lam_neither i u v huv hiu hiv
        rw [hx]; exact Or.inr (Or.inr (Or.inl rfl))
  · by_cases hiu : i = u
    · rw [hiu]
      have hx : sigma u * lamNeg u v huv * sigma u = rho u v huv :=
        Commons.GroupTheory.FreeGroup.sigma_conj_lamNeg_left u v huv
      rw [hx]; exact Or.inl rfl
    · by_cases hiv : i = v
      · rw [hiv]
        have hx : sigma v * lamNeg u v huv * sigma v = lam u v huv :=
          Commons.GroupTheory.FreeGroup.sigma_conj_lamNeg_right u v huv
        rw [hx]; exact Or.inr (Or.inr (Or.inl rfl))
      · have hx : sigma i * lamNeg u v huv * sigma i = lamNeg u v huv :=
          Commons.GroupTheory.FreeGroup.sigma_conj_lamNeg_neither i u v huv hiu hiv
        rw [hx]; exact Or.inr (Or.inr (Or.inr rfl))

/-- Conjugation by `sigma i` preserves `sEdgeOf u v` setwise. -/
lemma sigma_conj_sEdgeOf_mem {m : ℕ} {i u v : Fin m} (huv : u ≠ v)
    {g : MulAut (FreeGroup (Fin m))} (hg : g ∈ sEdgeOf u v huv) :
    sigma i * g * sigma i ∈ sEdgeOf u v huv := by
  rw [mem_sEdgeOf] at hg ⊢
  rcases hg with hg | hg
  · exact Or.inl (sigma_conj_dirEdge_mem huv hg)
  · exact Or.inr (sigma_conj_dirEdge_mem (huv := huv.symm) hg)

/-- Conjugation by `sigma i` preserves `SEdge p` setwise. -/
lemma sigma_conj_SEdge_mem {m : ℕ} (i : Fin m) {p : Edge m}
    {g : MulAut (FreeGroup (Fin m))} (hg : g ∈ SEdge p) :
    sigma i * g * sigma i ∈ SEdge p := by
  rw [SEdge_def] at hg ⊢
  exact sigma_conj_sEdgeOf_mem (ne_of_lt p.2) hg

/-- **Conjugation by `sigma i` permutes `SEdge p`**: the image of `SEdge p` under
`MulAut.conj (sigma i)` is `SEdge p` itself (it is a permutation of the eight
transvections of the edge, since conjugation by `sigma i` is an involution). -/
lemma SEdge_image_conj_sigma {m : ℕ} (i : Fin m) (p : Edge m) :
    (SEdge p).image (MulAut.conj (sigma i)) = SEdge p := by
  apply Finset.Subset.antisymm
  · rw [Finset.image_subset_iff]
    intro g hg
    rw [MulAut.conj_apply]
    exact sigma_conj_SEdge_mem i hg
  · intro x hx
    rw [Finset.mem_image]
    refine ⟨sigma i * x * sigma i, sigma_conj_SEdge_mem i hx, ?_⟩
    rw [MulAut.conj_apply, sigma_inv]
    exact Commons.GroupTheory.FreeGroup.sigma_conj_invol i x

/-! ## Products of conjugations -/

/-- The image of a set under a product `f * g` of automorphisms is the image under
`f` of the image under `g` (multiplication in `MulAut _` is composition). -/
lemma image_mul_eq {m : ℕ} {S : Finset (MulAut (FreeGroup (Fin m)))}
    (f g : MulAut (MulAut (FreeGroup (Fin m)))) :
    S.image (f * g) = (S.image g).image f := by
  have hfun : (⇑(f * g) : MulAut (FreeGroup (Fin m)) → MulAut (FreeGroup (Fin m)))
      = ⇑f ∘ ⇑g := by
    funext x
    simp only [MulAut.mul_apply, Function.comp_apply]
  rw [hfun, Finset.image_image]

/-- The image of `SEdge p` under conjugation by a product of single-generator
inversions is `SEdge p`. -/
lemma SEdge_image_conj_sigma_prod {m : ℕ} (L : List (Fin m)) (p : Edge m) :
    (SEdge p).image (MulAut.conj ((L.map (fun k => sigma k)).prod)) = SEdge p := by
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil,
      show MulAut.conj (1 : MulAut (FreeGroup (Fin m))) = 1 from
        (MulAut.conj (G := MulAut (FreeGroup (Fin m)))).map_one]
    ext x
    simp only [Finset.mem_image, MulAut.one_apply, exists_eq_right]
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons,
      show MulAut.conj (sigma a * (List.map (fun k => sigma k) L).prod)
          = MulAut.conj (sigma a) * MulAut.conj ((List.map (fun k => sigma k) L).prod) from
        (MulAut.conj (G := MulAut (FreeGroup (Fin m)))).map_mul _ _]
    rw [image_mul_eq, ih, SEdge_image_conj_sigma]

/-- **A sign flip preserves every edge transvection set**: `signAut s` is a product
of single-generator inversions, each of which preserves `SEdge p`. -/
lemma SEdge_image_conj_signAut {m : ℕ} (s : Fin m → Bool) (p : Edge m) :
    (SEdge p).image (MulAut.conj (signAut s)) = SEdge p := by
  have h : signAut s = (((List.finRange m).filter (fun k => s k)).map (fun k => sigma k)).prod :=
    rfl
  rw [h]
  exact SEdge_image_conj_sigma_prod _ p

/-- Conjugation by `permAut σ`, written with `MulAut.conj`. -/
lemma SEdge_image_conjAut {m : ℕ} (σ : Equiv.Perm (Fin m)) (p : Edge m) :
    (SEdge p).image (MulAut.conj (permAut σ)) = SEdge (σ • p) := by
  have h : conjFun σ
      = (⇑(MulAut.conj (permAut σ)) : MulAut (FreeGroup (Fin m)) → MulAut (FreeGroup (Fin m))) := by
    funext g; rw [MulAut.conj_apply]; rfl
  rw [← h]
  exact SEdge_image_conj σ p

/-! ## The theorem -/

theorem sigAutConjSEdge (r : ℕ) (p : Equiv.Perm (Fin r)) (s : Fin r → Bool)
    (e : Submission.RouteB.Edge r) :
    Finset.image (MulAut.conj (Submission.PTCert.sigAut p s)) (Submission.RouteB.Edge.SEdge e)
      = Submission.RouteB.Edge.SEdge (p • e) := by
  have hconj : MulAut.conj (sigAut p s)
      = MulAut.conj (signAut s) * MulAut.conj (permAut p) := by
    change MulAut.conj (signAut s * permAut p)
      = MulAut.conj (signAut s) * MulAut.conj (permAut p)
    exact (MulAut.conj (G := MulAut (FreeGroup (Fin r)))).map_mul (signAut s) (permAut p)
  rw [hconj, image_mul_eq, SEdge_image_conjAut p e]
  exact SEdge_image_conj_signAut s (p • e)

end Work.PTCert

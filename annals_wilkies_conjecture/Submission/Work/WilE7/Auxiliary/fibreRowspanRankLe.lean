import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic

namespace Work.WilE7.Aux

theorem fibreRowspanRankLe {p q : ℕ} {j j' r r' : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (c' : WilkiesDesign.E.EAChain (p + q) r') (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r)
    (h' : Fin j' → WilkiesDesign.E.EAPoly (p + q) r') (z : Fin (p + q) → ℝ)
    (hrank : (Matrix.of fun (a : Fin j) (l : Fin q) =>
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a)) z).rank = j)
    (hrank' : (Matrix.of fun (b : Fin j') (l : Fin q) =>
        WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z).rank = j')
    (hrow : ∀ a : Fin j, ∃ lam : Fin j' → ℝ, ∀ l : Fin q,
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a)) z
      = ∑ b, lam b * WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z) :
    j ≤ j' := by
  classical
  -- The `j × q` matrix of the `h`-directions and the `j' × q` matrix of the `h'`-directions.
  let M : Matrix (Fin j) (Fin q) ℝ := Matrix.of fun (a : Fin j) (l : Fin q) =>
      WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a)) z
  let N : Matrix (Fin j') (Fin q) ℝ := Matrix.of fun (b : Fin j') (l : Fin q) =>
      WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z
  have hrankM : M.rank = j := hrank
  have hrankN : N.rank = j' := hrank'
  -- `hrow` exhibits `M` as `L * N` for the `j × j'` matrix of coefficients.
  let L : Matrix (Fin j) (Fin j') ℝ := Matrix.of fun a b => Classical.choose (hrow a) b
  have hMN : M = L * N := by
    ext a l
    rw [Matrix.mul_apply]
    simp only [M, N, L, Matrix.of_apply]
    exact Classical.choose_spec (hrow a) l
  -- Rank is submultiplicative, so `rank M ≤ rank N`.
  have hle : M.rank ≤ N.rank := by
    rw [hMN]
    exact Matrix.rank_mul_le_right L N
  omega

end Work.WilE7.Aux

import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.Defs
import Submission.Work.WilE3K.ET_step
import Submission.Work.WilE3K.ET_base
import Submission.Work.WilE3K.ET_all_tight
import Submission.Work.WilE3K.ETB_le_poly
import Submission.Work.WilE3K.ET_sphere
import Submission.Work.WilE3K.ET_good_exists
import Submission.Work.WilE3K.ET_rolle_step
import Submission.Work.WilE3K.newData_degree
import Submission.Work.WilE2.regular_values_dense

namespace Work.WilE3K

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Two small pieces of arithmetic

`eval_mono_nat`: evaluation of a polynomial with coefficients in `ℕ` is monotone, which is what
lets the recursion bound `ETB` absorb the slack of the degree bookkeeping, and
`one_le_totalDegree_R`: every chain polynomial allowed by `SepKhovanskiiET` (`X` or `1 + X ^ 2`)
has total degree at least one, which bounds the number `rt` of lifted `tan` coordinates by the
degree sum appearing in the frozen statement. -/

/-- Evaluation of a polynomial with coefficients in `ℕ` is monotone. -/
private lemma eval_mono_nat (p : Polynomial ℕ) : Monotone fun x => p.eval x := by
  intro a b hab
  show p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum_range (p := p) a, Polynomial.eval_eq_sum_range (p := p) b]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

/-- Every chain polynomial of the two allowed types has total degree at least one. -/
private lemma one_le_totalDegree_R (R : MvPolynomial (Fin 1) ℝ)
    (hR : R = MvPolynomial.X 0 ∨ R = 1 + MvPolynomial.X 0 ^ 2) : 1 ≤ R.totalDegree := by
  rcases hR with h | h
  · rw [h]; simp
  · rw [h]
    have hmem : (Finsupp.single (0 : Fin 1) 2) ∈
        (1 + MvPolynomial.X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) ℝ).support := by
      rw [MvPolynomial.mem_support_iff]
      have hsing : (Finsupp.single (0 : Fin 1) 2 : Fin 1 →₀ ℕ) ≠ 0 :=
        Finsupp.single_eq_zero.not.mpr (by norm_num)
      have h1 : (1 : MvPolynomial (Fin 1) ℝ).coeff (Finsupp.single (0 : Fin 1) 2) = 0 := by
        rw [MvPolynomial.coeff_one]
        rw [if_neg]
        intro hcon
        exact hsing hcon.symm
      have h2 : (MvPolynomial.X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) ℝ).coeff
          (Finsupp.single (0 : Fin 1) 2) = 1 := by
        rw [MvPolynomial.coeff_X_pow]
        norm_num
      rw [MvPolynomial.coeff_add, h1, h2]
      norm_num
    have h3 := MvPolynomial.le_totalDegree hmem
    norm_num at h3
    omega

/-! ## The Sard input

`SepKhovanskiiET_of_parts` proves the corrected separable Khovanskii bound for exp/tan chains from
four inputs: the frozen exp-affine Khovanskii bound `hE2`, the arctan lift `hlift`, the ET
induction scheme `hET` and the polynomial domination `hbound` of the recursion bound.  The only
mathematical input not among those four is the density of regular values of a `C²` map
`ℝ^{m+1} → ℝ^m` (Sard's theorem in the codimension-one case): the ET induction's generic-value
step (`ET_good_exists`) needs it to make the level set of the remaining system a manifold.

It is isolated here as `sard_input`, so that it can be instantiated by the workspace's proof of
Sard's theorem (area E2, `Work.WilE2.regular_values_dense`) without touching the assembly below. -/
/-- **The density of regular values of a `C²` map `ℝ^{m+1} → ℝ^m`** (Sard's theorem in the
codimension-one case), as needed by the generic-value step of the ET induction.  This is the
theorem `Work.WilE2.regular_values_dense` of area E2 (proved from `RegVals.sard_codim_one`). -/
theorem sard_input :
    ∀ (m : ℕ) (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)), ContDiff ℝ 2 G →
      ∀ (y₀ : Fin m → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin m → ℝ, dist y y₀ < ε ∧
        ∀ z, G z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => G w a) z) :=
  fun m G hG => Work.WilE2.regular_values_dense G hG

/-! ## The assembly -/

/-- **The assembly of `SepKhovanskiiET` from the four parts.**  This is `SepKhovanskiiET_of_parts`
with the Sard input `hsard` made explicit; the four inputs `hE2`, `hlift`, `hET`, `hbound` are
exactly those of the requested theorem.

The `n = 0` case is degenerate (`Fin 0 → ℝ` is a subsingleton).  For `n > 0` the lift `hlift`
turns the separable chain into a lifted system `E` with `rt + re = r` arctan/exp chains, the ET
induction `hET` — whose base case is `hE2` through `ET_base` and whose step is `ET_step` applied to
the sphere step `ET_sphere`, the generic-value step `ET_good_exists`, the Rolle step `ET_rolle_step`
and the degree bookkeeping `newData_degree` — bounds its nondegenerate zeros by
`ETB q rt (rt + n - 1)`, and `hbound` dominates that recursion bound by a polynomial in the degree
sum. -/
theorem sepKhovanskiiET_of_parts_aux
    (hsard : ∀ (m : ℕ) (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)), ContDiff ℝ 2 G →
      ∀ (y₀ : Fin m → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin m → ℝ, dist y y₀ < ε ∧
        ∀ z, G z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => G w a) z))
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (f : Fin k → WilkiesDesign.E.EAPoly k r) (s : Finset (Fin k → ℝ)), k + r ≤ F →
      (∀ x ∈ s, (∀ i, WilkiesDesign.E.eaEval c (f i) x = 0) ∧
        (Matrix.of fun i j => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j (f i)) x).det ≠ 0) →
      s.card ≤ p.eval (∑ i, WilkiesDesign.E.atomDeg (f i)))
    (hlift : ∀ {n r : ℕ} (S : Work.WilE3.SepChainLocal n r) (f : Fin n → WilkiesDesign.E.EAPoly n r)
      (D : Set (Fin n → ℝ)) (s : Finset (Fin n → ℝ)) (hpos : 0 < n)
      (htype : ∀ j, (S.phi j = Real.exp ∧ S.R j = MvPolynomial.X 0) ∨
        (S.phi j = Real.tan ∧ S.R j = 1 + MvPolynomial.X 0 ^ 2))
      (hD : Convex ℝ D)
      (hdom : ∀ x ∈ D, ∀ j, (∑ i, S.a j i * x i + S.b j) ∈ S.dom j)
      (hsD : (↑s : Set (Fin n → ℝ)) ⊆ D)
      (hnd : ∀ x ∈ s, Work.WilE3.SepChainLocal.Nondegen S f x),
      ∃ (rt re : ℕ) (E : Work.WilE3K.ETData (rt + n - 1) rt n re)
        (t : Finset (Fin ((rt + n - 1) + 1) → ℝ)),
        rt + re = r ∧ t.card = s.card ∧ (∀ z ∈ t, E.Nondegen z) ∧
        (∑ i, WilkiesDesign.E.atomDeg (E.G i)) ≤ (∑ i, WilkiesDesign.E.atomDeg (f i)))
    (hET : ∀ (q : Polynomial ℕ) (M : ℕ),
      (∀ (N n re : ℕ) (E : Work.WilE3K.ETData N 0 n re) (s : Finset (Fin (N + 1) → ℝ)),
        N + 1 + re ≤ M → (∀ z ∈ s, E.Nondegen z) →
          s.card ≤ q.eval (∑ i, WilkiesDesign.E.atomDeg (E.G i))) →
      (∀ (rt N n re : ℕ) (E : Work.WilE3K.ETData N (rt + 1) n re)
        (s : Finset (Fin (N + 1) → ℝ)), N + 1 + re + (rt + 1) ≤ M →
        (∀ z ∈ s, E.Nondegen z) →
        ∃ (E' : Work.WilE3K.ETData (N + 1) rt (n + 2) re) (t : Finset (Fin ((N + 1) + 1) → ℝ)),
          (∀ z ∈ t, E'.Nondegen z) ∧ s.card ≤ t.card ∧
          (∑ i, WilkiesDesign.E.atomDeg (E'.G i)) + rt ≤
            (N + 9) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 11)) →
      ∀ (rt N n re : ℕ) (E : Work.WilE3K.ETData N rt n re) (s : Finset (Fin (N + 1) → ℝ)),
        N + 1 + re + rt ≤ M → (∀ z ∈ s, E.Nondegen z) →
        s.card ≤ Work.WilE3K.ETB q rt N (∑ i, WilkiesDesign.E.atomDeg (E.G i) + rt))
    (hbound : ∀ (q : Polynomial ℕ) (F : ℕ), ∃ p : Polynomial ℕ,
      ∀ (rt N D : ℕ), N + 1 + rt ≤ F → Work.WilE3K.ETB q rt N D ≤ p.eval D) :
    ∀ F : ℕ, Work.WilE3K.SepKhovanskiiET F := by
  intro F
  -- The base case of the ET induction: the frozen exp-affine Khovanskii bound `q`.
  obtain ⟨q, hq⟩ := hE2 (2 * F + 2)
  have hbase : ∀ (N n re : ℕ) (E : Work.WilE3K.ETData N 0 n re) (s : Finset (Fin (N + 1) → ℝ)),
      N + 1 + re ≤ 2 * F + 2 → (∀ z ∈ s, E.Nondegen z) →
        s.card ≤ q.eval (∑ i, WilkiesDesign.E.atomDeg (E.G i)) :=
    fun N n re E s hM hs => ET_base q (2 * F + 2) hq N n re E s hs hM
  -- The generic-value step, from the Sard input.
  have hgood' : ∀ {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
      (s : Finset (Fin (N + 1) → ℝ)), (∀ z ∈ s, E.Nondegen z) → IsProperMap E.psiMap →
      ∃ (y : Fin N → ℝ) (ρ : ℝ), E.ETGood y ∧ 0 < ρ ∧ dist (E.psiLift y) 0 < ρ ∧
        ∀ y' : Fin (N + 1) → ℝ, dist y' 0 < ρ →
          ∃ t : Finset (Fin (N + 1) → ℝ), t.card = s.card ∧ ∀ z ∈ t, E.map z = y' := by
    intro N rt n re E s hs hp
    exact ET_good_exists E s hs hp hsard
  -- The Rolle step, from the generic-value data.  The degree part of `ET_rolle_step` is not
  -- needed here: `ET_step` carries the degree bookkeeping separately (`newData_degree`).
  have hrolle' : ∀ {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
      (s : Finset (Fin (N + 1) → ℝ)), (∀ z ∈ s, E.Nondegen z) → IsProperMap E.psiMap →
      ∀ (y : Fin N → ℝ) (ρ : ℝ), E.ETGood y → 0 < ρ → dist (E.psiLift y) 0 < ρ →
        (∀ y' : Fin (N + 1) → ℝ, dist y' 0 < ρ →
          ∃ t : Finset (Fin (N + 1) → ℝ), t.card = s.card ∧ ∀ z ∈ t, E.map z = y') →
        ∃ (δ : ℝ) (t : Finset (Fin (N + 1) → ℝ)),
          (∀ z ∈ t, (E.newData y δ).Nondegen z) ∧ s.card ≤ t.card := by
    intro N rt n re E s hs hp y ρ hgy hρ hρd hift
    obtain ⟨δ, t, hnd', hcard, _⟩ := ET_rolle_step E s hs hp ρ hρ hift y hgy hρd
    exact ⟨δ, t, hnd', hcard⟩
  -- One elimination step: sphere step, generic value, Rolle step and the degree bookkeeping,
  -- assembled by `ET_step`.
  have hstep : ∀ (rt N n re : ℕ) (E : Work.WilE3K.ETData N (rt + 1) n re)
      (s : Finset (Fin (N + 1) → ℝ)), N + 1 + re + (rt + 1) ≤ 2 * F + 2 →
      (∀ z ∈ s, E.Nondegen z) →
      ∃ (E' : Work.WilE3K.ETData (N + 1) rt (n + 2) re) (t : Finset (Fin ((N + 1) + 1) → ℝ)),
        (∀ z ∈ t, E'.Nondegen z) ∧ s.card ≤ t.card ∧
        (∑ i, WilkiesDesign.E.atomDeg (E'.G i)) + rt ≤
          (N + 9) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 11) := by
    intro rt N n re E s _ hs
    exact ET_step (N := N) (rt := rt) (n := n) (re := re) newData_degree ET_sphere
      hgood' hrolle' E s hs
  -- The recursion bound is dominated by a polynomial in the degree sum.
  obtain ⟨pb, hpb⟩ := hbound q (2 * F + 2)
  refine ⟨pb + 1, ?_⟩
  intro n r S f D s hnF htype hconv hdom hsD hnd
  by_cases hn : n = 0
  · -- `n = 0`: `Fin 0 → ℝ` is a subsingleton, so `s.card ≤ 1`.
    subst hn
    have hcard : s.card ≤ 1 :=
      Finset.card_le_one.mpr fun a _ b _ => by funext i; exact i.elim0
    have h1 : 1 ≤ (pb + 1).eval (∑ i : Fin 0, WilkiesDesign.E.atomDeg (f i) +
        ∑ j : Fin r, (S.R j).totalDegree) := by
      rw [Polynomial.eval_add, Polynomial.eval_one]
      exact Nat.succ_le_succ (Nat.zero_le _)
    exact le_trans hcard h1
  · -- `n > 0`: lift the separable chain, then run the ET induction.
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨rt, re, E, t, hrtre, htcard, hndE, hdegE⟩ :=
      hlift S f D s hnpos htype hconv hdom hsD hnd
    have hM' : (rt + n - 1) + 1 + re + rt ≤ 2 * F + 2 := by omega
    have hET' := hET q (2 * F + 2) hbase hstep rt (rt + n - 1) n re E t hM' hndE
    have hFb : (rt + n - 1) + 1 + rt ≤ 2 * F + 2 := by omega
    have hbnd := hpb rt (rt + n - 1) (∑ i, WilkiesDesign.E.atomDeg (E.G i) + rt) hFb
    -- the degree bookkeeping: `rt` is dominated by `∑ j, (S.R j).totalDegree`
    have hR1 : ∀ j : Fin r, 1 ≤ (S.R j).totalDegree := by
      intro j
      rcases htype j with ⟨_, hR⟩ | ⟨_, hR⟩
      · exact one_le_totalDegree_R (S.R j) (Or.inl hR)
      · exact one_le_totalDegree_R (S.R j) (Or.inr hR)
    have hsumR : r ≤ ∑ j : Fin r, (S.R j).totalDegree := by
      have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
        (f := fun _ : Fin r => (1 : ℕ)) (g := fun j => (S.R j).totalDegree)
        (fun j _ => hR1 j)
      simpa using h
    have hrtle : rt ≤ ∑ j : Fin r, (S.R j).totalDegree := by omega
    have hmono : pb.eval (∑ i, WilkiesDesign.E.atomDeg (E.G i) + rt) ≤
        pb.eval (∑ i : Fin n, WilkiesDesign.E.atomDeg (f i) +
          ∑ j : Fin r, (S.R j).totalDegree) :=
      eval_mono_nat pb (by omega)
    calc s.card = t.card := htcard.symm
      _ ≤ ETB q rt (rt + n - 1) (∑ i, WilkiesDesign.E.atomDeg (E.G i) + rt) := hET'
      _ ≤ pb.eval (∑ i, WilkiesDesign.E.atomDeg (E.G i) + rt) := hbnd
      _ ≤ pb.eval (∑ i : Fin n, WilkiesDesign.E.atomDeg (f i) +
            ∑ j : Fin r, (S.R j).totalDegree) := hmono
      _ ≤ (pb + 1).eval (∑ i : Fin n, WilkiesDesign.E.atomDeg (f i) +
            ∑ j : Fin r, (S.R j).totalDegree) := by
          rw [Polynomial.eval_add, Polynomial.eval_one]
          exact Nat.le_succ _

/-- **The corrected separable Khovanskii bound for exp/tan chains, assembled from its parts**
(design `sources/wilkiesE3E9/wilkies_E3E9_gaps.md`, §GAP 1, nodes K1–K3): the frozen exp-affine
Khovanskii bound `hE2`, the arctan lift `hlift`, the ET induction scheme `hET` (base case `hE2` via
`ET_base`, step = one sphere-and-Rolle arctan elimination) and the polynomial domination `hbound`
of the recursion bound `ETB` imply `SepKhovanskiiET`.

The only mathematical input besides the four parts is Sard's theorem in the codimension-one case
(`sard_input`), used to produce a regular value of the remaining system in the elimination step. -/
theorem SepKhovanskiiET_of_parts
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (f : Fin k → WilkiesDesign.E.EAPoly k r) (s : Finset (Fin k → ℝ)), k + r ≤ F →
      (∀ x ∈ s, (∀ i, WilkiesDesign.E.eaEval c (f i) x = 0) ∧
        (Matrix.of fun i j => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j (f i)) x).det ≠ 0) →
      s.card ≤ p.eval (∑ i, WilkiesDesign.E.atomDeg (f i)))
    (hlift : ∀ {n r : ℕ} (S : Work.WilE3.SepChainLocal n r) (f : Fin n → WilkiesDesign.E.EAPoly n r)
      (D : Set (Fin n → ℝ)) (s : Finset (Fin n → ℝ)) (hpos : 0 < n)
      (htype : ∀ j, (S.phi j = Real.exp ∧ S.R j = MvPolynomial.X 0) ∨
        (S.phi j = Real.tan ∧ S.R j = 1 + MvPolynomial.X 0 ^ 2))
      (hD : Convex ℝ D)
      (hdom : ∀ x ∈ D, ∀ j, (∑ i, S.a j i * x i + S.b j) ∈ S.dom j)
      (hsD : (↑s : Set (Fin n → ℝ)) ⊆ D)
      (hnd : ∀ x ∈ s, Work.WilE3.SepChainLocal.Nondegen S f x),
      ∃ (rt re : ℕ) (E : Work.WilE3K.ETData (rt + n - 1) rt n re)
        (t : Finset (Fin ((rt + n - 1) + 1) → ℝ)),
        rt + re = r ∧ t.card = s.card ∧ (∀ z ∈ t, E.Nondegen z) ∧
        (∑ i, WilkiesDesign.E.atomDeg (E.G i)) ≤ (∑ i, WilkiesDesign.E.atomDeg (f i)))
    (hET : ∀ (q : Polynomial ℕ) (M : ℕ),
      (∀ (N n re : ℕ) (E : Work.WilE3K.ETData N 0 n re) (s : Finset (Fin (N + 1) → ℝ)),
        N + 1 + re ≤ M → (∀ z ∈ s, E.Nondegen z) →
          s.card ≤ q.eval (∑ i, WilkiesDesign.E.atomDeg (E.G i))) →
      (∀ (rt N n re : ℕ) (E : Work.WilE3K.ETData N (rt + 1) n re)
        (s : Finset (Fin (N + 1) → ℝ)), N + 1 + re + (rt + 1) ≤ M →
        (∀ z ∈ s, E.Nondegen z) →
        ∃ (E' : Work.WilE3K.ETData (N + 1) rt (n + 2) re) (t : Finset (Fin ((N + 1) + 1) → ℝ)),
          (∀ z ∈ t, E'.Nondegen z) ∧ s.card ≤ t.card ∧
          (∑ i, WilkiesDesign.E.atomDeg (E'.G i)) + rt ≤
            (N + 9) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 11)) →
      ∀ (rt N n re : ℕ) (E : Work.WilE3K.ETData N rt n re) (s : Finset (Fin (N + 1) → ℝ)),
        N + 1 + re + rt ≤ M → (∀ z ∈ s, E.Nondegen z) →
        s.card ≤ Work.WilE3K.ETB q rt N (∑ i, WilkiesDesign.E.atomDeg (E.G i) + rt))
    (hbound : ∀ (q : Polynomial ℕ) (F : ℕ), ∃ p : Polynomial ℕ,
      ∀ (rt N D : ℕ), N + 1 + rt ≤ F → Work.WilE3K.ETB q rt N D ≤ p.eval D) :
    ∀ F : ℕ, Work.WilE3K.SepKhovanskiiET F :=
  sepKhovanskiiET_of_parts_aux sard_input hE2 hlift hET hbound

end Work.WilE3K

import Mathlib
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.root_height_bound
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.height_ge_one
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.finite_algebraic_bounded_deg_height
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_eval_ne_zero_of_transcendental
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_natDegree_map_eq
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_one_le

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial
open scoped BigOperators

noncomputable section

/-- The inline naive height of an algebraic number, as a natural. -/
private def Hgt (α : ℂ) : ℕ :=
  let p := minpoly ℚ α
  let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val)
  Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs)

/-- sup-norm of the coefficient vector of an integer polynomial, mapped to the reals. -/
private abbrev supN (S : Polynomial ℤ) : ℝ := (S.map (Int.castRingHom ℝ)).supNorm

/-- An integer polynomial seen over the complexes. -/
private abbrev Sℂ (S : Polynomial ℤ) : Polynomial ℂ := S.map (Int.castRingHom ℂ)

/-- value of an integer polynomial at a real point (as a real number). -/
private abbrev pv (ξ : ℝ) (S : Polynomial ℤ) : ℝ := Polynomial.eval ξ (S.map (Int.castRingHom ℝ))

/-! ### Generic real/multiset lemmas -/

/-- Norm of a product over a mapped multiset of complex numbers is the product of the
norms (complex norm is multiplicative). -/
private lemma multiset_norm_prod_map (s : Multiset ℂ) (g : ℂ → ℂ) :
    ‖(s.map g).prod‖ = (s.map (fun β : ℂ => ‖g β‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]

/-- Product of nonnegative reals is nonnegative. -/
private lemma multiset_prod_nonneg (s : Multiset ℝ) (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact mul_nonneg (h a (Multiset.mem_cons_self a s))
      (ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)))

/-- If every element of a nonempty list of reals is strictly larger than the positive
`T`, then the product of the list is strictly larger than `T ^ length`. -/
private lemma list_pow_lt_prod_of_lt {T : ℝ} (hT : 0 < T) :
    ∀ {l : List ℝ}, l ≠ [] → (∀ a ∈ l, T < a) → T ^ l.length < l.prod := by
  intro l
  induction l with
  | nil =>
    intro hne _
    simp at hne
  | cons a l ih =>
    intro hne hgt
    have ha : T < a := hgt a (by simp)
    by_cases hl : l = []
    · subst hl
      simp [ha]
    · have hne' : l ≠ [] := hl
      have hgt' : ∀ b ∈ l, T < b := by
        intro b hb
        exact hgt b (by simp [hb])
      have hrec : T ^ l.length < l.prod := ih hne' hgt'
      have hlen0 : 0 ≤ T ^ l.length := pow_nonneg hT.le l.length
      have hprod0 : 0 < l.prod := lt_of_le_of_lt hlen0 hrec
      calc
        T ^ (l.length + 1) = T * T ^ l.length := by rw [pow_succ]; ring
        _ < T * l.prod := by
          exact mul_lt_mul_of_pos_left hrec hT
        _ ≤ a * l.prod := by
          exact mul_le_mul_of_nonneg_right (le_of_lt ha) hprod0.le
        _ = (a :: l).prod := by simp

/-- Multiset version of the strict power/product comparison. -/
private lemma multiset_pow_lt_prod_of_lt {s : Multiset ℂ} {T : ℝ} (hT : 0 < T) (hs : s ≠ 0)
    (f : ℂ → ℝ) (hgt : ∀ β ∈ s, T < f β) : T ^ s.card < (s.map f).prod := by
  have hs' : s.toList ≠ [] := by
    intro hz
    apply hs
    have hc : s.card = 0 := by
      rw [← Multiset.length_toList s, hz, List.length_nil]
    exact Multiset.card_eq_zero.mp hc
  have hs'' : s.toList.map f ≠ [] := by
    intro hz
    exact hs' (List.map_eq_nil_iff.mp hz)
  have hgtl : ∀ a ∈ s.toList.map f, T < a := by
    intro a ha
    rcases (List.mem_map.mp ha) with ⟨b, hb, rfl⟩
    exact hgt b ((Multiset.mem_toList.mp) hb)
  have hmain := list_pow_lt_prod_of_lt hT (l := s.toList.map f) hs'' hgtl
  rw [List.length_map, Multiset.length_toList, Multiset.prod_map_toList] at hmain
  exact hmain

/-- If a product of distances over a nonempty multiset is bounded above by `T^N`, then
some element is at distance at most `T`. -/
private lemma exists_le_of_prod_le_pow {s : Multiset ℂ} {x : ℂ} {T : ℝ} (hT0 : 0 < T)
    (hT1 : T ≤ 1) {N : ℕ} (hs : s ≠ 0) (hcard : s.card ≤ N)
    (hprod : (s.map (fun β : ℂ => ‖x - β‖)).prod ≤ T ^ N) : ∃ β, β ∈ s ∧ ‖x - β‖ ≤ T := by
  by_contra hnot
  have hgt : ∀ β ∈ s, T < ‖x - β‖ := by
    intro β hβ
    exact lt_of_not_ge (by
      intro hle
      exact hnot ⟨β, hβ, hle⟩)
  have hstr : T ^ s.card < (s.map (fun β : ℂ => ‖x - β‖)).prod :=
    multiset_pow_lt_prod_of_lt hT0 hs (fun β : ℂ => ‖x - β‖) hgt
  have hpowle : T ^ N ≤ T ^ s.card := pow_le_pow_of_le_one hT0.le hT1 hcard
  have hlt : T ^ N < (s.map (fun β : ℂ => ‖x - β‖)).prod := lt_of_le_of_lt hpowle hstr
  exact (not_lt_of_ge hprod) hlt

/-! ### Polynomial lemmas -/

/-- A nonzero integer has complex norm at least one. -/
private lemma int_norm_cast_complex_one_le (c : ℤ) (hc : c ≠ 0) : (1 : ℝ) ≤ ‖(c : ℂ)‖ := by
  have hre : (((c : ℤ) : ℂ).re) = (c : ℝ) := by simp
  have habs : (1 : ℝ) ≤ |(c : ℝ)| := by
    rw [← Int.cast_abs (R := ℝ)]
    have hz : (0 : ℤ) < |c| := abs_pos.mpr hc
    have h1 : (1 : ℤ) ≤ |c| := (Int.add_one_le_iff.mpr hz)
    exact_mod_cast h1
  have hle : |(c : ℝ)| ≤ ‖((c : ℤ) : ℂ)‖ := by
    rw [← hre]
    exact Complex.abs_re_le_norm ((c : ℤ) : ℂ)
  exact le_trans habs hle

/-- The norm (over ℂ) of the leading coefficient of a nonzero integer polynomial is at
least `1`. -/
private lemma int_poly_leadingCoeff_norm_one_le (S : Polynomial ℤ) (hS : S ≠ 0) :
    (1 : ℝ) ≤ ‖(Sℂ S).leadingCoeff‖ := by
  have hc0 : S.leadingCoeff ≠ 0 := by
    intro hz
    exact hS ((Polynomial.leadingCoeff_eq_zero).mp hz)
  have hcast : (Sℂ S).leadingCoeff = (S.leadingCoeff : ℂ) := by
    dsimp [Sℂ]
    simpa using (Polynomial.leadingCoeff_map_of_injective (f := Int.castRingHom ℂ) Int.cast_injective S)
  rw [hcast]
  exact int_norm_cast_complex_one_le S.leadingCoeff hc0

/-- The complex evaluation of an integer polynomial at the real `ξ` equals the real
evaluation embedded in the complexes. -/
private lemma eval_complex_eq (S : Polynomial ℤ) (ξ : ℝ) :
    Polynomial.eval ((ξ : ℝ) : ℂ) (Sℂ S) =
      (algebraMap ℝ ℂ) (Polynomial.eval ξ (S.map (Int.castRingHom ℝ))) := by
  dsimp [Sℂ]
  have hcomp : Int.castRingHom ℂ = (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) := by
    ext z
    rfl
  rw [hcomp]
  rw [Polynomial.eval_map]
  rw [← Polynomial.eval₂_map]
  simpa [aeval_def] using (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (R := ℝ) (A := ℂ)
    (x := ξ) (p := S.map (Int.castRingHom ℝ)))

/-- The complex norm of the complex evaluation equals the real norm of the real
evaluation. -/
private lemma eval_norm_complex_eq (S : Polynomial ℤ) (ξ : ℝ) :
    ‖Polynomial.eval ((ξ : ℝ) : ℂ) (Sℂ S)‖ = ‖Polynomial.eval ξ (S.map (Int.castRingHom ℝ))‖ := by
  rw [eval_complex_eq]
  simp

/-- The product (over the complex roots of `S`, with multiplicity) of the distances from
`x` is bounded above by the norm of the value `S(x)`. -/
private lemma roots_prod_le_eval (S : Polynomial ℤ) (hS : S ≠ 0) (x : ℂ) :
    ((Sℂ S).roots.map (fun β : ℂ => ‖x - β‖)).prod ≤ ‖(Sℂ S).eval x‖ := by
  have hF : Sℂ S ≠ 0 := by
    dsimp [Sℂ]
    exact (Polynomial.map_eq_zero_iff (f := Int.castRingHom ℂ) Int.cast_injective).not.mpr hS
  have heq := (IsAlgClosed.splits (Sℂ S)).eval_eq_prod_roots x
  rw [heq, norm_mul]
  have hnorm : ‖((Sℂ S).roots.map (fun β : ℂ => x - β)).prod‖ =
      ((Sℂ S).roots.map (fun β : ℂ => ‖x - β‖)).prod :=
    multiset_norm_prod_map (Sℂ S).roots (fun β => x - β)
  rw [hnorm]
  calc
    ((Sℂ S).roots.map (fun β : ℂ => ‖x - β‖)).prod
        ≤ 1 * ((Sℂ S).roots.map (fun β : ℂ => ‖x - β‖)).prod := by rw [one_mul]
    _ ≤ ‖(Sℂ S).leadingCoeff‖ * ((Sℂ S).roots.map (fun β : ℂ => ‖x - β‖)).prod := by
        exact mul_le_mul_of_nonneg_right (int_poly_leadingCoeff_norm_one_le S hS)
          (multiset_prod_nonneg ((Sℂ S).roots.map (fun β : ℂ => ‖x - β‖)) (by
            intro a ha
            rcases (Multiset.mem_map.mp ha) with ⟨β, hβ, rfl⟩
            exact norm_nonneg (x - β)))

/-! ### Root transfer -/

/-- From one integer polynomial `S` of degree `≤ n` with very small value at the real
transcendental `ξ` (namely `‖S(ξ)‖ ≤ ‖S‖^(-n(w+2))`) and with `‖S‖ ≥ 2`, one can find a
complex root `α` of `S` such that `‖ξ - α‖ ≤ ‖S‖^(-(w+2))`. -/
private lemma transfer_small (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (w : ℝ) (hw : 0 < w)
    (S : Polynomial ℤ) (hS : S ≠ 0) (hdeg : S.natDegree ≤ n) (hsup : 2 ≤ supN S)
    (hval : ‖pv ξ S‖ ≤ (supN S) ^ (-((n : ℝ) * (w + 2)))) :
    ∃ α : ℂ, Polynomial.IsRoot (Sℂ S) α ∧ ‖(ξ : ℂ) - α‖ ≤ (supN S) ^ (-(w + 2)) := by
  classical
  let s : ℝ := supN S
  let F : Polynomial ℂ := Sℂ S
  let E : ℝ := (n : ℝ) * (w + 2)
  let T : ℝ := s ^ (-(w + 2))
  have hs1 : 1 ≤ s := by
    dsimp [s, supN]
    exact int_poly_supNorm_one_le S hS
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hT0 : 0 < T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos hs0 _
  have hT1 : T ≤ 1 := by
    dsimp [T]
    have hexp : -(w + 2) ≤ (0 : ℝ) := by linarith
    simpa using (Real.rpow_le_rpow_of_exponent_le hs1 hexp)
  have hE : s ^ (-E) = T ^ n := by
    dsimp [T, E]
    calc
      s ^ (-((n : ℝ) * (w + 2))) = s ^ ((-(w + 2)) * (n : ℝ)) := by congr 1; ring
      _ = (s ^ (-(w + 2))) ^ (n : ℝ) := Real.rpow_mul (le_of_lt hs0) (-(w + 2)) (n : ℝ)
      _ = (s ^ (-(w + 2))) ^ n := by rw [Real.rpow_natCast]
  -- S is nonconstant
  have hdegS1 : 1 ≤ S.natDegree := by
    by_contra hlt
    have hd0 : S.natDegree = 0 := by omega
    have hconst : S = Polynomial.C (S.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hsval : ‖pv ξ S‖ = s := by
      dsimp [pv, s, supN]
      rw [hconst]
      rw [Polynomial.map_C, Polynomial.supNorm_C]
      simp
    have hsmall : ‖pv ξ S‖ ≤ 1 := by
      have hE1 : (-E : ℝ) ≤ 0 := by dsimp [E]; linarith
      have hb : s ^ (-E) ≤ 1 := by
        simpa using (Real.rpow_le_rpow_of_exponent_le hs1 hE1)
      exact le_trans (by simpa [s, E] using hval) hb
    have : (2 : ℝ) ≤ 1 := by
      calc
        (2 : ℝ) ≤ s := hsup
        _ = ‖pv ξ S‖ := hsval.symm
        _ ≤ 1 := hsmall
    linarith
  -- roots of F: nonempty, cardinality = natDegree ≤ n
  have hF0 : F ≠ 0 := by
    dsimp [F, Sℂ]
    exact (Polynomial.map_eq_zero_iff (f := Int.castRingHom ℂ) Int.cast_injective).not.mpr hS
  have hd_eq : F.roots.card = F.natDegree := IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := F)
  have hd : 1 ≤ F.roots.card := by
    rw [hd_eq]
    dsimp [F]
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective S]
    exact hdegS1
  have hroots_ne : F.roots ≠ 0 := by
    intro hz
    have : F.roots.card = 0 := by simp [hz]
    omega
  have hcard : F.roots.card ≤ n := by
    rw [hd_eq]
    dsimp [F]
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective S]
    exact hdeg
  -- product bound chain
  have hprod0 : ((Sℂ S).roots.map (fun β : ℂ => ‖(ξ : ℂ) - β‖)).prod ≤ ‖(Sℂ S).eval (ξ : ℂ)‖ :=
    roots_prod_le_eval S hS (ξ : ℂ)
  have hnorm : ‖(Sℂ S).eval (ξ : ℂ)‖ = ‖pv ξ S‖ := eval_norm_complex_eq S ξ
  have hval2 : ‖(Sℂ S).eval (ξ : ℂ)‖ ≤ s ^ (-E) := by
    rw [hnorm]
    simpa [s, E] using hval
  have hprod : ((Sℂ S).roots.map (fun β : ℂ => ‖(ξ : ℂ) - β‖)).prod ≤ T ^ n := by
    calc
      ((Sℂ S).roots.map (fun β : ℂ => ‖(ξ : ℂ) - β‖)).prod
          ≤ ‖(Sℂ S).eval (ξ : ℂ)‖ := hprod0
      _ ≤ s ^ (-E) := hval2
      _ ≤ T ^ n := by
        rw [hE]
  -- apply the multiset lemma
  rcases (exists_le_of_prod_le_pow (s := F.roots) (x := (ξ : ℂ)) (T := T) hT0 hT1
    (N := n) hroots_ne hcard (by simpa [F] using hprod)) with ⟨β, hβmem, hβle⟩
  refine ⟨β, ?_, ?_⟩
  · -- IsRoot F β
    exact (Polynomial.mem_roots (p := F) hF0).mp hβmem
  · -- distance bound
    simpa [F, T, s] using hβle

/-! ### Real-power and algebraic/transcendental helper lemmas -/

/-- For `1 ≤ N ≤ s`, `s` to a negative power is at most `N` to the same power. -/
private lemma rpow_antitone_base {s N : ℝ} (w : ℝ) (hw : 0 < w) (hN1 : 1 ≤ N)
    (hNs : N ≤ s) : s ^ (-(w + 2)) ≤ N ^ (-(w + 2)) := by
  have hs0 : 0 < s := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hN1) hNs
  have hw2 : 0 ≤ w + 2 := by linarith
  have hNw : N ^ (w + 2) ≤ s ^ (w + 2) := Real.rpow_le_rpow (by linarith) hNs hw2
  have hNwpos : 0 < N ^ (w + 2) := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN1) _
  calc
    s ^ (-(w + 2)) = (s ^ (w + 2))⁻¹ := by rw [Real.rpow_neg (le_of_lt hs0)]
    _ ≤ (N ^ (w + 2))⁻¹ := by
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hs0 _) hNwpos).mpr hNw
    _ = N ^ (-(w + 2)) := by rw [Real.rpow_neg (le_of_lt (lt_of_lt_of_le zero_lt_one hN1))]

/-- From `H ≥ 1`, `H ≤ C·s` and `s ≥ C^(w+1)` we get `s^(-(w+2)) ≤ H^(-w-1)`. -/
private lemma final_rpow {H s C : ℝ} (w : ℝ) (hw : 0 < w) (hH1 : 1 ≤ H) (hC0 : 0 < C)
    (hCs : H ≤ C * s) (hCw : C ^ (w + 1) ≤ s) (hs1 : 1 ≤ s) :
    s ^ (-(w + 2)) ≤ H ^ (-w - 1) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH1
  have hw1 : 0 ≤ w + 1 := by linarith
  have h1 : H ^ (w + 1) ≤ (C * s) ^ (w + 1) := by
    exact Real.rpow_le_rpow hH0.le hCs hw1
  have h2 : (C * s) ^ (w + 1) = C ^ (w + 1) * s ^ (w + 1) := by
    rw [Real.mul_rpow hC0.le hs0.le]
  have h3 : C ^ (w + 1) * s ^ (w + 1) ≤ s * s ^ (w + 1) := by
    exact mul_le_mul_of_nonneg_right hCw (by positivity : 0 ≤ s ^ (w + 1))
  have h4 : s * s ^ (w + 1) = s ^ (w + 2) := by
    calc
      s * s ^ (w + 1) = s ^ (w + 1) * s := by ring
      _ = s ^ (w + 1) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ ((w + 1) + (1 : ℝ)) := by rw [← Real.rpow_add hs0]
      _ = s ^ (w + 2) := by congr 1; ring
  have hAB : H ^ (w + 1) ≤ s ^ (w + 2) := by
    calc
      H ^ (w + 1) ≤ (C * s) ^ (w + 1) := h1
      _ = C ^ (w + 1) * s ^ (w + 1) := h2
      _ ≤ s * s ^ (w + 1) := h3
      _ = s ^ (w + 2) := h4
  have hs2 : 0 < s ^ (w + 2) := Real.rpow_pos_of_pos hs0 _
  have hH2 : 0 < H ^ (w + 1) := Real.rpow_pos_of_pos hH0 _
  calc
    s ^ (-(w + 2)) = (s ^ (w + 2))⁻¹ := by rw [Real.rpow_neg hs0.le]
    _ ≤ (H ^ (w + 1))⁻¹ := (inv_le_inv₀ hs2 hH2).mpr hAB
    _ = H ^ (-(w + 1)) := by rw [Real.rpow_neg hH0.le]
    _ = H ^ (-w - 1) := by congr 1; ring

/-- If `N` is larger than `(1/ε)^(1/(w+2))`, then `N^(-(w+2)) < ε`. -/
private lemma strict_small (w : ℝ) (hw : 0 < w) {ε N : ℝ} (hε : 0 < ε)
    (hN : (1 / ε) ^ (1 / (w + 2)) < N) : N ^ (-(w + 2)) < ε := by
  have hx0 : 0 < (1 / ε) ^ (1 / (w + 2)) := Real.rpow_pos_of_pos (by positivity) _
  have hN0 : 0 < N := lt_trans hx0 hN
  have hw2 : 0 < w + 2 := by linarith
  have hpow1 : ((1 / ε) ^ (1 / (w + 2))) ^ (w + 2) < N ^ (w + 2) :=
    Real.rpow_lt_rpow hx0.le hN hw2
  have hpow2 : ((1 / ε) ^ (1 / (w + 2))) ^ (w + 2) = 1 / ε := by
    calc
      ((1 / ε) ^ (1 / (w + 2))) ^ (w + 2)
          = (1 / ε) ^ ((1 / (w + 2)) * (w + 2)) := by
              rw [← Real.rpow_mul (by positivity : 0 ≤ 1 / ε)]
      _ = (1 / ε) ^ (1 : ℝ) := by congr 1; field_simp
      _ = 1 / ε := by rw [Real.rpow_one]
  have hlt : 1 / ε < N ^ (w + 2) := by
    rw [← hpow2]
    exact hpow1
  have hinv : (N ^ (w + 2))⁻¹ < (1 / ε)⁻¹ := by
    exact (inv_lt_inv₀ (Real.rpow_pos_of_pos hN0 _) (by positivity : 0 < 1 / ε)).mpr hlt
  calc
    N ^ (-(w + 2)) = (N ^ (w + 2))⁻¹ := by rw [Real.rpow_neg hN0.le]
    _ < (1 / ε)⁻¹ := hinv
    _ = ε := by rw [one_div, inv_inv]

/-- Polynomials over ℚ: evaluating after mapping to ℂ at a real point equals the real
evaluation embedded in ℂ. -/
private lemma rat_poly_eval_complex_eq (p : Polynomial ℚ) (ξ : ℝ) :
    Polynomial.eval ((ξ : ℝ) : ℂ) (p.map (algebraMap ℚ ℂ)) =
      (algebraMap ℝ ℂ) (Polynomial.eval ξ (p.map (algebraMap ℚ ℝ))) := by
  have hcomp : algebraMap ℚ ℂ = (algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ) := by
    ext z
    simp
  calc
    Polynomial.eval ((ξ : ℝ) : ℂ) (p.map (algebraMap ℚ ℂ))
        = Polynomial.eval₂ (algebraMap ℚ ℂ) ((ξ : ℝ) : ℂ) p := by
            rw [Polynomial.eval_map]
    _ = Polynomial.eval₂ ((algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ)) ((ξ : ℝ) : ℂ) p := by
            rw [hcomp]
    _ = Polynomial.eval₂ (algebraMap ℝ ℂ) ((ξ : ℝ) : ℂ) (p.map (algebraMap ℚ ℝ)) := by
            rw [← Polynomial.eval₂_map]
    _ = (algebraMap ℝ ℂ) (Polynomial.eval ξ (p.map (algebraMap ℚ ℝ))) := by
            simpa using (Polynomial.eval₂_hom (f := algebraMap ℝ ℂ) (x := ξ)
              (p := p.map (algebraMap ℚ ℝ)))

/-- If a real number is algebraic over ℚ as a complex number then it is algebraic over ℚ
as a real number. -/
private lemma isAlgebraic_real_of_complex (ξ : ℝ) (hξc : IsAlgebraic ℚ (ξ : ℂ)) :
    IsAlgebraic ℚ ξ := by
  rcases hξc with ⟨p, hp, hp0⟩
  refine ⟨p, hp, ?_⟩
  change Polynomial.eval₂ (algebraMap ℚ ℝ) ξ p = 0
  rw [← map_eq_zero_iff (algebraMap ℝ ℂ) Complex.ofReal_injective]
  rw [← Polynomial.eval_map]
  rw [← rat_poly_eval_complex_eq p ξ]
  rw [Polynomial.eval_map]
  change Polynomial.aeval ((ξ : ℝ) : ℂ) p = 0
  exact hp0

/-- A root of a nonzero integer polynomial is not equal to a transcendental real `ξ`. -/
private lemma dist_root_pos (ξ : ℝ) (hξ : Transcendental ℚ ξ) (S : Polynomial ℤ) (hS : S ≠ 0)
    (α : ℂ) (hroot : Polynomial.IsRoot (Sℂ S) α) : 0 < ‖(ξ : ℂ) - α‖ := by
  have hpv0 : pv ξ S ≠ 0 := int_poly_eval_ne_zero_of_transcendental ξ hξ S hS
  have hF0 : (Sℂ S).eval (ξ : ℂ) ≠ 0 := by
    intro hz
    apply hpv0
    have hn : ‖pv ξ S‖ = 0 := by
      rw [← eval_norm_complex_eq S ξ, hz]
      simp
    exact (norm_eq_zero.mp hn)
  have hαne : α ≠ (ξ : ℂ) := by
    intro hαeq
    have hF0' : (Sℂ S).eval α ≠ 0 := by
      rw [← hαeq] at hF0
      exact hF0
    exact hF0' ((Polynomial.IsRoot.def).mp hroot)
  exact (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hαne)))

theorem root_transfer_all_heights (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (hWoo : ∀ E : ℝ, 0 < E → ∀ N : ℝ, 0 < N → ∃ S : Polynomial ℤ, S ≠ 0 ∧
      S.natDegree ≤ n ∧ N ≤ (S.map (Int.castRingHom ℝ)).supNorm ∧
      ‖Polynomial.eval ξ (S.map (Int.castRingHom ℝ))‖ ≤
        ((S.map (Int.castRingHom ℝ)).supNorm) ^ (-E)) :
    ∀ w : ℝ, 0 < w → ∀ h0 : ℕ, ∃ α : ℂ,
      IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
      0 < ‖(ξ : ℂ) - α‖ ∧
      (h0 : ℝ) ≤ ((((let p := minpoly ℚ α;
          let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
          Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ))) ∧
      ‖(ξ : ℂ) - α‖ ≤
        ((((let p := minpoly ℚ α;
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ))) ^
          (-w - 1) := by
  change ∀ w : ℝ, 0 < w → ∀ h0 : ℕ, ∃ α : ℂ,
    IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
    0 < ‖(ξ : ℂ) - α‖ ∧ (h0 : ℝ) ≤ (Hgt α : ℝ) ∧
    ‖(ξ : ℂ) - α‖ ≤ (Hgt α : ℝ) ^ (-w - 1)
  intro w hw h0
  classical
  rcases root_height_bound n with ⟨C, hC0, hC⟩
  let E : ℝ := (n : ℝ) * (w + 2)
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  let B : Set ℂ := {a | IsAlgebraic ℚ a ∧ Polynomial.natDegree (minpoly ℚ a) ≤ n ∧ Hgt a < h0}
  have hBfin : B.Finite := by
    have hF : {a : ℂ | IsAlgebraic ℚ a ∧ Polynomial.natDegree (minpoly ℚ a) ≤ n ∧
        Hgt a ≤ h0}.Finite := by
      simpa [Hgt] using (finite_algebraic_bounded_deg_height n h0)
    exact hF.subset (by
      intro a ha
      exact ⟨ha.1, ha.2.1, Nat.le_of_lt ha.2.2⟩)
  -- The standard construction: from any sufficiently large bound N produce an
  -- algebraic number α with the distance and height bounds (except h0 ≤ height).
  have produce : ∀ N : ℝ, 2 ≤ N → C ^ (w + 1) ≤ N →
      ∃ α : ℂ, IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
        0 < ‖(ξ : ℂ) - α‖ ∧ ‖(ξ : ℂ) - α‖ ≤ N ^ (-(w + 2)) ∧
        ‖(ξ : ℂ) - α‖ ≤ (Hgt α : ℝ) ^ (-w - 1) := by
    intro N hN2 hNC
    rcases hWoo E hEpos N (by linarith) with ⟨S, hSne, hSdeg, hSsup, hSval⟩
    have hNsup : N ≤ supN S := by simpa [supN] using hSsup
    have hs2 : 2 ≤ supN S := le_trans hN2 hNsup
    have hvalS : ‖pv ξ S‖ ≤ (supN S) ^ (-E) := by
      simpa [E, supN, pv] using hSval
    rcases (transfer_small n (by omega : 1 ≤ n) ξ w hw S hSne hSdeg hs2 hvalS)
      with ⟨α, hroot, hdist⟩
    rcases (hC S α hSne hSdeg hroot) with ⟨hαalg, hαdeg, hαH⟩
    have hHgt : (Hgt α : ℝ) ≤ C * supN S := by
      simpa [Hgt, supN] using hαH
    have hH1 : 1 ≤ (Hgt α : ℝ) := by
      simpa [Hgt] using (height_ge_one α hαalg)
    have hsup1 : 1 ≤ supN S := int_poly_supNorm_one_le S hSne
    have hfin := final_rpow w hw hH1 hC0 hHgt (le_trans hNC hNsup) hsup1
    have hNle : (supN S) ^ (-(w + 2)) ≤ N ^ (-(w + 2)) :=
      rpow_antitone_base w hw (by linarith) hNsup
    have hdistN : ‖(ξ : ℂ) - α‖ ≤ N ^ (-(w + 2)) := le_trans hdist hNle
    have hdistF : ‖(ξ : ℂ) - α‖ ≤ (Hgt α : ℝ) ^ (-w - 1) := le_trans hdist hfin
    have hdist0 : 0 < ‖(ξ : ℂ) - α‖ := dist_root_pos ξ hξ S hSne α hroot
    refine ⟨α, hαalg, hαdeg, hdist0, hdistN, hdistF⟩
  by_cases hB : B = ∅
  · -- B empty: heights are automatically ≥ h0 for every algebraic α of degree ≤ n
    let N0 : ℝ := max 2 (C ^ (w + 1))
    have hN02 : 2 ≤ N0 := by
      dsimp [N0]
      exact le_max_left 2 (C ^ (w + 1))
    have hN0C : C ^ (w + 1) ≤ N0 := by
      dsimp [N0]
      exact le_max_right 2 (C ^ (w + 1))
    rcases (produce N0 hN02 hN0C) with ⟨α, hαalg, hαdeg, hdist0, _hdistN, hfinal⟩
    have hHh0 : (h0 : ℝ) ≤ (Hgt α : ℝ) := by
      have hh0 : h0 ≤ Hgt α := by
        by_contra hnot
        have hlt : Hgt α < h0 := Nat.lt_of_not_ge hnot
        have hmem : α ∈ B := ⟨hαalg, hαdeg, hlt⟩
        rw [hB] at hmem
        simp at hmem
      exact_mod_cast hh0
    exact ⟨α, hαalg, hαdeg, hdist0, hHh0, hfinal⟩
  · -- B nonempty: pick a large N so that any produced root has height ≥ h0
    have hBne : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hB
    rcases hBne with ⟨a0, ha0⟩
    let Fs : Finset ℂ := hBfin.toFinset
    have ha0Fs : a0 ∈ Fs := (hBfin.mem_toFinset).mpr ha0
    let D : Finset ℝ := Fs.image (fun a => ‖(ξ : ℂ) - a‖)
    have hDne : D.Nonempty := by
      refine ⟨‖(ξ : ℂ) - a0‖, ?_⟩
      exact Finset.mem_image.mpr ⟨a0, ha0Fs, rfl⟩
    let ε : ℝ := D.min' hDne
    have hεpos : 0 < ε := by
      have hm : ε ∈ D := by
        dsimp [ε]
        exact Finset.min'_mem D hDne
      rcases (Finset.mem_image.mp hm) with ⟨a, haFs, hfeq⟩
      rw [← hfeq]
      have haB : a ∈ B := (hBfin.mem_toFinset).mp haFs
      rcases haB with ⟨halg, _hdeg, _hHlt⟩
      have hneq : a ≠ (ξ : ℂ) := by
        intro hξa
        have hcx : IsAlgebraic ℚ (ξ : ℂ) := by
          rw [← hξa]
          exact halg
        exact hξ (isAlgebraic_real_of_complex ξ hcx)
      have hnorm_ne : ‖(ξ : ℂ) - a‖ ≠ 0 := by
        intro hz
        have hEq : (ξ : ℂ) = a := sub_eq_zero.mp (norm_eq_zero.mp hz)
        exact hneq hEq.symm
      exact lt_of_le_of_ne (norm_nonneg ((ξ : ℂ) - a)) (Ne.symm hnorm_ne)
    have hεle : ∀ a ∈ B, ε ≤ ‖(ξ : ℂ) - a‖ := by
      intro a haB
      have haFs : a ∈ Fs := (hBfin.mem_toFinset).mpr haB
      have hD : ‖(ξ : ℂ) - a‖ ∈ D := Finset.mem_image.mpr ⟨a, haFs, rfl⟩
      dsimp [ε]
      exact Finset.min'_le D ‖(ξ : ℂ) - a‖ hD
    let Nε : ℝ := max 2 (max (C ^ (w + 1)) ((1 / ε) ^ (1 / (w + 2))))
    let N : ℝ := Nε + 1
    have hN2 : 2 ≤ N := by
      dsimp [N, Nε]
      have : 2 ≤ Nε := le_max_left 2 (max (C ^ (w + 1)) ((1 / ε) ^ (1 / (w + 2))))
      linarith
    have hNC : C ^ (w + 1) ≤ N := by
      dsimp [N, Nε]
      have h1 : C ^ (w + 1) ≤ max (C ^ (w + 1)) ((1 / ε) ^ (1 / (w + 2))) :=
        le_max_left _ _
      have h2 : max (C ^ (w + 1)) ((1 / ε) ^ (1 / (w + 2))) ≤ Nε :=
        le_max_right 2 _
      have h3 : Nε ≤ Nε + 1 := by linarith
      exact le_trans (le_trans h1 h2) h3
    have hNε : (1 / ε) ^ (1 / (w + 2)) < N := by
      dsimp [N, Nε]
      have h1 : (1 / ε) ^ (1 / (w + 2)) ≤ max (C ^ (w + 1)) ((1 / ε) ^ (1 / (w + 2))) :=
        le_max_right _ _
      have h2 : max (C ^ (w + 1)) ((1 / ε) ^ (1 / (w + 2))) ≤ Nε :=
        le_max_right 2 _
      have h3 : Nε < Nε + 1 := by linarith
      exact lt_of_le_of_lt (le_trans h1 h2) h3
    rcases (produce N hN2 hNC) with ⟨α, hαalg, hαdeg, hdist0, hdistN, hfinal⟩
    have hsmall : ‖(ξ : ℂ) - α‖ < ε :=
      lt_of_le_of_lt hdistN (strict_small w hw hεpos hNε)
    have hαnotB : α ∉ B := by
      intro hmem
      have hle := hεle α hmem
      linarith
    have hHh0 : (h0 : ℝ) ≤ (Hgt α : ℝ) := by
      have hh0 : h0 ≤ Hgt α := by
        by_contra hnot
        have hlt : Hgt α < h0 := Nat.lt_of_not_ge hnot
        exact hαnotB ⟨hαalg, hαdeg, hlt⟩
      exact_mod_cast hh0
    exact ⟨α, hαalg, hαdeg, hdist0, hHh0, hfinal⟩

end

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree

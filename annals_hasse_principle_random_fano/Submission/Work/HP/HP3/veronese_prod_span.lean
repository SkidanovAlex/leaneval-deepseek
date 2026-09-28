import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP3.VeroProdDefs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.lam_latOrth_veronese_le

namespace Work.HP.HP3

open Work.HP

/-- With a single variable (`n = 0`) a degree-`d` monomial is determined by the sum condition
`∑ i, m i = d`, so `Mon d 0` is a subsingleton. -/
lemma subsingleton_Mon_zero_vars (d : ℕ) : Subsingleton (Mon d 0) := by
  refine ⟨fun a b => Subtype.ext (funext fun i => Fin.ext ?_)⟩
  have hsum : ∀ m : Mon d 0, ((m.1 i : ℕ)) = d := by
    intro m
    have h := m.2
    rw [Finset.sum_eq_single i] at h
    · exact h
    · intro j _ hj
      exfalso
      apply hj
      apply Fin.ext
      have hj1 : (j : ℕ) < 1 := j.2
      have hi1 : (i : ℕ) < 1 := i.2
      omega
    · intro hh; exact absurd (Finset.mem_univ i) hh
  rw [hsum a, hsum b]

/-- The degree-`d` forms `X^m · ⟨c_j, X⟩` (`m : Mon (d-1) n`, `j : Fin n`), for `c_j` linearly
independent vectors of `latOrth x`, span (over `ℝ`) the whole space of degree-`d` forms vanishing
at `x`, i.e. the kernel of `evalLin d n x` (equivalently `(ℝ ν_{d,n}(x))^⊥`).

Suggested route.  `⊆` follows from `veronese_prod_api` (each generator pairs to
`ν_{d-1,n}(x)(m) * ⟨c_j, x⟩ = 0`).  For `⊇`: `latOrth x = x^⊥ ∩ ℤ^{n+1}` has ℤ-rank `n`
(`x ≠ 0` by `IsPrim`), the `c_j` are ℝ-independent by `hcli`, so their ℝ-span is all of `x^⊥`;
hence it suffices to show that the `ℝ`-span `V` of `{X^m · L : m, L ∈ x^⊥}` is the kernel
(which has dimension `NN d n - 1`, since `evalLin` is nonzero).  For that pick `i₀` with
`x i₀ ≠ 0` and use the reduction: for a monomial `X^{m'}` with `m' ≠ d • e_{i₀}`, choose `j ≠ i₀`
with `m'_j ≥ 1` and write, for the linear form `L = x_{i₀} X_j - x_j X_{i₀} ∈ x^⊥`,
`X^{m'} = (1/x_{i₀}) X^{m' - e_j} L + (x_j/x_{i₀}) X^{m' - e_j + e_{i₀}}`;
iterating strictly decreases the exponent outside the `i₀`-th coordinate, so all monomials except
`X_{i₀}^d` lie in `V`, and `X_{i₀}^d` does not (its value at `x` is `x_{i₀}^d ≠ 0`).  Hence
`V` has dimension `NN d n - 1` and equals the kernel, which is a submodule of the span of the
generators (the generators with `c = L` are among the required ones, since
`x_{i₀} e_j - x_j e_{i₀} ∈ latOrth x`, and the missing directions are produced by `hcli`). -/
theorem veronese_prod_span (d n : ℕ) (hd : 2 ≤ d) (x : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (c : Fin n → (Fin (n + 1) → ℤ)) (hc : ∀ j, c j ∈ latOrth x) (hcli : LinearIndependent ℤ c) :
    Submodule.span ℝ (Set.range (fun p : Mon (d - 1) n × Fin n => prodVecR d n p.1 (c p.2)))
      = LinearMap.ker (evalLin d n x) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- The only degenerate case: `n = 0` (a single variable, no generators `c j`).
    subst hn0
    haveI : Subsingleton (Mon d 0) := subsingleton_Mon_zero_vars d
    have hx0 : x ≠ 0 := Vero.isPrim_ne_zero hx
    have hx00 : x 0 ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
      have hiz : i = 0 := by
        apply Fin.ext
        have hi2 := i.2
        omega
      subst hiz
      simpa using hi
    have hL : Submodule.span ℝ
        (Set.range (fun p : Mon (d - 1) 0 × Fin 0 => prodVecR d 0 p.1 (c p.2))) = ⊥ := by
      refine le_antisymm ?_ bot_le
      rw [Submodule.span_le]
      rintro y ⟨⟨m, j⟩, -⟩
      exact Fin.elim0 j
    have hR : LinearMap.ker (evalLin d 0 x) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro F hF
      rw [LinearMap.mem_ker] at hF
      rw [Submodule.mem_bot]
      have hν : Vero.veroneseR d 0 x (Vero.powMon d 0 0) ≠ 0 := by
        have h1 : veronese d 0 x (Vero.powMon d 0 0) = x 0 ^ d :=
          Vero.veronese_powMon d 0 0 x
        have h2 : ((veronese d 0 x (Vero.powMon d 0 0) : ℤ) : ℝ) ≠ 0 := by
          rw [h1]
          exact_mod_cast pow_ne_zero d hx00
        simpa only [Vero.veroneseR] using h2
      have hsum : evalLin d 0 x F
          = F (Vero.powMon d 0 0) * Vero.veroneseR d 0 x (Vero.powMon d 0 0) := by
        simp only [evalLin, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_eq_single (Vero.powMon d 0 0)]
        · simp [Vero.veroneseR]
        · intro m _ hm; exact absurd (Subsingleton.elim m _) hm
        · intro h; exact absurd (Finset.mem_univ _) h
      have hfa : F (Vero.powMon d 0 0) = 0 := by
        have h := hF
        rw [hsum] at h
        exact (mul_eq_zero.mp h).resolve_right hν
      funext m'
      rw [Pi.zero_apply, show m' = Vero.powMon d 0 0 from Subsingleton.elim m' _]
      exact hfa
    rw [hL, hR]
  · -- `n ≥ 1`: this is exactly the (proved) general span statement.
    exact Vero.prodVec_span_eq_ker d n hd hn x hx c hc hcli

end Work.HP.HP3

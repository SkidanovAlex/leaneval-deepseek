import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.clo_lemma8
import Submission.Work.Higman.MSA.l8_setup
import Submission.Work.Higman.MSA.l8_step1
import Submission.Work.Higman.MSA.l8_card
import Submission.Work.Higman.MSA.l8_BV
import Submission.Work.Higman.MSA.l8_betaV
import Submission.Work.Higman.MSA.l8_mult_core

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.Higman

/-- The hard case of Higman's Lemma 8: with `A ≠ ⊥` and `A ^ (2) ≠ ⊥` in the situation of
`clo_lemma8`/`higman_lemma8` there is a contradiction.  This is the last gap of Higman's Lemma 8:
`Submission/Work/Higman/clo_lemma8.lean` already contains the full case split
(`A = ⊥`, `A ^ (2) = ⊥`, else this result) and declares the present result as `clo_hard` with a
`sorry` (untouched since 19:05); `Submission/Work/Higman/higman_lemma8.lean` and
`Submission/Work/Higman/higman_lemma8_new.lean` are the same result with a `sorry`.  Restating it
at a fresh path lets a colleague close it in parallel.  (Note: `open scoped commutatorElement` is
needed for `⁅C, C⁆` to elaborate.)

Route (see `Submission/Work/Higman/NOTES_clo_lemma8.md`, steps 1-3).  `Ω₁(P) ≤ A`, `C ^ (2) = A`
(`powSub_C_eq_of_cover`), and `⁅A ^ (2 ^ k), C⁆ = A ^ (2 ^ (k + 1))`
(`commutator_powSub_A_C`) give the lower central series `C > A > A² > A⁴ > ⋯`, so the four
`𝔽₂⟨ξ⟩`-modules `V = C/A`, `W = Ω₁(P) ≅ A/A² ≅ A²/A⁴` are all of order `q = 2 ^ n` (`n ≥ 2`),
with `ξ` acting transitively on their non-zero vectors (`Fq_structure`, `h.trans`).  On them the
squaring map `s : V → W`, its polar form `B`, and the bracket `β : V × W → W` are well defined,
`ξ`-equivariant and biadditive, with `s` anisotropic, `B` alternating and non-zero, `β x (s x) = 0`
and `β ≠ 0` (because `A ≠ A²` and `A² ≠ A⁴`).  These are precisely the hypotheses of the purely
algebraic result `Work.Higman.core_alt_pairing` (proved, in
`Submission/Work/Higman/core_alt_pairing_new.lean`; it has the same hypothesis list as
`Work.Higman.clo_core`), which yields `False`.  The well-definedness and biadditivity steps are
available in `clo_setup` and `clo_quot`. -/
theorem clo_hard_v2 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = A)
    (hA0 : A ≠ ⊥) (hA2 : Work.Higman.powSub A 2 ≠ ⊥) : False := by
  classical
  haveI hAn : A.Normal := hA.normal
  -- ## Step 1: `Ω₁(P) ≤ A` and the exponent data of the homocyclic group `A`
  have hOmega : omega1 P ≤ A := omega1_le_of_isXiAbelNormal_ne_bot h hA hA0
  obtain ⟨e, he2, he1, htopA, hkey⟩ := MSA.l8_setup h hA hA0 hA2 hOmega
  have he : 1 ≤ e := by omega
  let S : MSA.L8.D h A C :=
    { hA := hA, hCn := hCn, hCinv := hCinv, hAC := hAC, hCA := hCA, hcover := hcover,
      hC2 := hC2, hCd := hCd, hAne := hA0, hOmega := hOmega, e := e, he := he, he2 := he2,
      he1 := he1, htopA := htopA, hkey := hkey }
  -- ## Step 2: the two elementary abelian groups have the same order `q = 2 ^ n`, `n ≥ 2`
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hn2 : 2 ≤ n := by
    have h4 := h.omega1_card_ge_four
    rw [hn] at h4
    by_contra hcon
    push_neg at hcon
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h1
    omega
  have htriv := MSA.L8.l8_xi_pow_card_sub_one_triv_quot (h := h) S
  have hcard := MSA.L8.l8_quot_card (h := h) S hn hn2 htriv
  -- ## Step 3: the algebraic properties of `sV`, `BV`, `betaV`
  obtain ⟨hSinj, -, hS1, hSxi, hSpol⟩ := MSA.L8.l8_sV (h := h) S hcard
  obtain ⟨-, hBV1, hBV2, hBVdiag, hBVxi, hBVne⟩ := MSA.L8.l8_BV (h := h) S
  obtain ⟨-, hβ1, hβ2, hβxi, hβrel, hβne⟩ := MSA.L8.l8_betaV (h := h) S
  -- ## Step 4: the two `ξ`-modules
  letI : CommGroup (↥C ⧸ (A.subgroupOf C)) :=
    { (inferInstance : Group (↥C ⧸ (A.subgroupOf C))) with mul_comm := MSA.L8.quot_comm hCd }
  letI : CommGroup ↥(omega1 P) :=
    { (inferInstance : Group ↥(omega1 P)) with
      mul_comm := fun a b => Subtype.ext (h.omega1_comm a.2 b.2) }
  have hW2 : ∀ w : ↥(omega1 P), w * w = 1 := by
    intro w
    apply Subtype.ext
    show (w : P) * (w : P) = 1
    rw [← pow_two]
    exact h.mem_omega1.mp w.2
  -- `ξ` is transitive on the non-identity elements of `Ω₁(P)`
  have hWtrans : ∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, ((xiZ h) ^ k) a = b := by
    intro a b ha hb
    have ha2 : orderOf ((a : ↥(omega1 P)) : P) = 2 :=
      omega1_orderOf_eq_two h a.2 (fun hc => ha (Subtype.ext hc))
    have hb2 : orderOf ((b : ↥(omega1 P)) : P) = 2 :=
      omega1_orderOf_eq_two h b.2 (fun hc => hb (Subtype.ext hc))
    obtain ⟨k, hk⟩ := h.trans _ _ ha2 hb2
    exact ⟨k, Subtype.ext (by rw [xiZ_pow_coe]; exact hk)⟩
  -- `ξ` is transitive on the non-identity elements of `C/A`, transported along the bijection `sV`
  have hSxipow : ∀ (k : ℕ) (x : ↥C ⧸ (A.subgroupOf C)),
      ((xiZ h) ^ k) (MSA.L8.sV S x)
        = MSA.L8.sV S (((MSA.L8.xiQuot h hA.map_eq hCinv) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, ih, hSxi]
        congr 1
        rw [pow_succ', MulAut.mul_apply]
  have hVtrans : ∀ a b : ↥C ⧸ (A.subgroupOf C), a ≠ 1 → b ≠ 1 →
      ∃ k : ℕ, ((MSA.L8.xiQuot h hA.map_eq hCinv) ^ k) a = b := by
    intro a b ha hb
    have hsa : MSA.L8.sV S a ≠ 1 := fun hc => ha (hSinj (by rw [hc, hS1]))
    have hsb : MSA.L8.sV S b ≠ 1 := fun hc => hb (hSinj (by rw [hc, hS1]))
    obtain ⟨k, hk⟩ := hWtrans (MSA.L8.sV S a) (MSA.L8.sV S b) hsa hsb
    exact ⟨k, hSinj (by rw [← hSxipow k a, hk])⟩
  -- ## Step 5: Higman's §4 Lemma 6 (multiplicative form)
  exact MSA.l8_mult_core (V := ↥C ⧸ (A.subgroupOf C)) (W := ↥(omega1 P))
    (fun v => MSA.L8.quot_sq_one (A := A) (C := C) hC2 v) hW2
    hn2 (hcard.trans hn) hn
    (MSA.L8.xiQuot h hA.map_eq hCinv) (xiZ h) hVtrans hWtrans
    (MSA.L8.BV S) hBV1 hBV2 hBVdiag hBVxi hBVne
    (MSA.L8.sV S) hS1 hSxi hSpol (fun a ha hc => ha (hSinj (by rw [hc, hS1])))
    (MSA.L8.betaV S) hβ1 hβ2 hβxi hβrel hβne

end Work.Higman

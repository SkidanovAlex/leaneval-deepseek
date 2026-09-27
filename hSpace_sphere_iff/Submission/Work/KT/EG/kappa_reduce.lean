import Mathlib
import Submission.Work.KT.EG.kappaRedDefs
import Submission.Work.KT.Fund.laurent_approx
import Submission.Work.KT.Fund.kappa_hopf
import Submission.Work.KT.EG.laurent_polar
import Submission.Work.KT.EG.kappa_twist_fund
import Submission.Work.KT.EG.kappa_linearise
import Submission.Work.KT.EG.kappa_lin_gen

namespace Work.KT.EG

open _root_.Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **The clutching reduction** ((D) of §3 of `Submission/Work/KT/Fund/NOTES_kappa.md`): every
clutched class is, up to the rank-`n` trivial class, an `K(X,ℂ)`-multiple of the Bott class `β`.

Route (Hatcher, *Vector Bundles and K-Theory* Thm 2.2, steps 2–4), using
`Work.KT.Fund.laurent_approx`, `Work.KT.Fund.kappa_homotopic`, `Work.KT.EG.kappa_lin` and Hatcher's
linearisation:

1. `Fund.laurent_approx` homotopes `u` to the image `P.map (laurentMap X)` of a matrix of Laurent
   polynomials; `kappa_homotopic` gives `κ u = κ (P.map (laurentMap X))`.
2. the twist `κ (z^m · u) = μ (κ u) (γ^m)` (`γ := snd* (cls hopfIdem)`) strips the negative powers:
   writing `P = z^{-N} q` with `q` polynomial, `κ (P.map ...) = μ (κ (q.map ...)) ((γ)^{-N})`.
3. Hatcher's linearisation (`[E,q] + n[E,1] ≈ [(n+1)E, L^n q]`, the companion matrix, homotopy by
   elementary row/column operations) reduces a polynomial clutching function to a *linear* one
   `z·1 + pullMat b`, at the price of adding multiples of `cls (Mat.one _ ·)`.
4. `kappa_lin` (with `E` the spectral projection of the linear part, `spectral_split_out`) evaluates
   that linear unit.
5. collecting the terms: every summand is either `cls (Mat.one _ r)` (which cancels against
   `cls (Mat.one _ n)` up to the rank shift, since `κ` is additive over block sums by `kappa_add`)
   or `μ (s b) γ`, and a `γ`-term with `b` of rank `m` equals `μ (s b') (β) + s b'` modulo the
   trivial classes.

Steps 2 and 3 have no lemmas in the library yet (they are the two independent inputs of this
statement); steps 1 and 4 are `laurent_approx` and `kappa_lin`. -/
theorem kappa_reduce (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ) :
    ∃ b : K0 C(X, ℂ),
      Work.KT.Fund.kappa X n u - cls (Mat.one C(X × S2, ℂ) n)
        = μ (K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ))
              (pullAlg (ContinuousMap.fst : C(X × S2, X))) b)
            (K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
                (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem)
              - cls (Mat.one C(X × S2, ℂ) 1)) := by
  change ∃ b : K0 C(X, ℂ), redK X n u = μ (fstStar X b) (betaHopf X)
  obtain ⟨P, hPun, H, hHun, hH0, hH1⟩ :=
    Work.KT.Fund.laurent_approx X n (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) u.isUnit
  -- the unit with values `P.map (laurentMap X)`
  let V : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ := hPun.unit
  have hVeq : (V : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = P.map (laurentMap X) :=
    IsUnit.unit_spec hPun
  have hH1' : ∀ (i j : Fin n) (x : X) (s : Sph ℂ), H i j ((x, s), 1) = V i j (x, s) := by
    intro i j x s
    rw [hVeq]
    exact hH1 i j x s
  -- step 1: homotopy invariance of `κ`
  have hκ : Work.KT.Fund.kappa X n u = Work.KT.Fund.kappa X n V :=
    kappa_homotopic_transport X n u V H hHun hH0 hH1'
  -- step 2: split off the polar part
  obtain ⟨N, q, hq⟩ := laurent_polar X n P
  let c : (C(X × Sph ℂ, ℂ))ˣ := (zUnit X) ^ (-(N : ℤ))
  have hcval : ((c : C(X × Sph ℂ, ℂ))) = ((zUnit X) ^ (-(N : ℤ)) : (C(X × Sph ℂ, ℂ))ˣ).val :=
    rfl
  let W : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ :=
    Units.map (Matrix.scalar (Fin n)).toMonoidHom c⁻¹ * V
  have hWval : (W : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = q.map (polyMap X) := by
    show (↑(Units.map (Matrix.scalar (Fin n)).toMonoidHom c⁻¹ * V) :
      Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = q.map (polyMap X)
    rw [Units.val_mul, Units.coe_map, hVeq, hq, ← hcval]
    show ((Matrix.scalar (Fin n)) ((c⁻¹ : (C(X × Sph ℂ, ℂ))ˣ) : C(X × Sph ℂ, ℂ)))
        * ((c : C(X × Sph ℂ, ℂ)) • (q.map (polyMap X))) = q.map (polyMap X)
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, smul_smul, Units.inv_mul, one_smul]
  have hVc : (V : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (c : C(X × Sph ℂ, ℂ)) • (W : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hVeq, hq, ← hcval, hWval]
  have htwist := kappa_twist_fund X n N W V hVc
  -- step 3: Hatcher's linearisation
  obtain ⟨m', a, b, D, hD, hred⟩ := kappa_linearise X n q W hWval
  -- step 4: the linear clutching function
  obtain ⟨b', hb'⟩ := kappa_lin_gen X m' a b D hD μ hμ
  -- step 5: collect the terms
  refine ⟨b' - (N * n) • cls (Mat.one C(X, ℂ) 1), ?_⟩
  have hbott : bottZ X = betaHopf X := by
    show Work.KT.Fund.kappa X 1 (Work.KT.Fund.zUnitMat X) - cls (Mat.one C(X × S2, ℂ) 1)
      = gammaHopf X - cls (Mat.one C(X × S2, ℂ) 1)
    rw [Work.KT.Fund.kappa_hopf X]
    rfl
  have hredκ : redK X n u = redK X n V := by
    show Work.KT.Fund.kappa X n u - cls (Mat.one C(X × S2, ℂ) n)
      = Work.KT.Fund.kappa X n V - cls (Mat.one C(X × S2, ℂ) n)
    rw [hκ]
  have hRHS : (μ (fstStar X (b' - (N * n) • cls (Mat.one C(X, ℂ) 1)))) (betaHopf X)
      = (μ (fstStar X b')) (betaHopf X) - (N * n) • betaHopf X := by
    have h1 : fstStar X (b' - (N * n) • cls (Mat.one C(X, ℂ) 1))
        = fstStar X b' - (N * n) • cls (Mat.one C(X × S2, ℂ) 1) := by
      rw [map_sub, map_nsmul, fstStar_cls_one]
    rw [h1]
    have h2 : ∀ y : K0 C(X × S2, ℂ),
        (μ (fstStar X b' - (N * n) • cls (Mat.one C(X × S2, ℂ) 1))) y
          = (μ (fstStar X b')) y
            - (N * n) • (μ (cls (Mat.one C(X × S2, ℂ) 1))) y := by
      intro y
      rw [map_sub, AddMonoidHom.sub_apply, map_nsmul]
      simp
    rw [h2, IsK0Mul.one_left (fun x y : C(X × S2, ℂ) => mul_comm x y) hμ (betaHopf X)]
  rw [hredκ, htwist, hred, hb', hbott, hRHS]

end

end Work.KT.EG

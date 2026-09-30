import Mathlib
import Submission.Work.Pi6.MSS.e2Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- `eqToHom` in `ModuleCat` between the cochain modules `Cochain 𝕜 X a` and `Cochain 𝕜 X b`
acts on elements as the type cast. -/
private lemma coch_eqToHom_apply {𝕜 : Type} [Field 𝕜] (X : SSet) {a b : ℕ} (h : a = b)
    (u : Work.Cohomology.Cochain 𝕜 X a) :
    (eqToHom (congrArg (fun t => ModuleCat.of 𝕜 (Work.Cohomology.Cochain 𝕜 X t)) h) :
        ModuleCat.of 𝕜 (Work.Cohomology.Cochain 𝕜 X a) ⟶
        ModuleCat.of 𝕜 (Work.Cohomology.Cochain 𝕜 X b)).hom u
      = h ▸ u := by
  subst h
  rfl

/-- The Alexander–Whitney cup product underlying the product of the Serre cochain filtration is
associative, in the transported form used by `CohFilt.xcast`. -/
theorem serreCF_xcast_mul (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (n m k : ℕ)
    (x : (serreCF 𝕜 E B p).C.X n) (y : (serreCF 𝕜 E B p).C.X m)
    (z : (serreCF 𝕜 E B p).C.X k) :
    (serreCF 𝕜 E B p).xcast (Nat.add_assoc n m k)
        ((serreCF 𝕜 E B p).mul (n+m) k ((serreCF 𝕜 E B p).mul n m x y) z)
      = (serreCF 𝕜 E B p).mul n (m+k) x ((serreCF 𝕜 E B p).mul m k y z) := by
  have hY : (serreCF 𝕜 E B p).xcast (Nat.add_assoc n m k)
        (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E)
          (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y) z)
      = (Nat.add_assoc n m k) ▸ (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E)
          (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y) z) :=
    coch_eqToHom_apply (Work.SSS.sSing E) (Nat.add_assoc n m k) _
  show (serreCF 𝕜 E B p).xcast (Nat.add_assoc n m k)
        (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E)
          (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y) z)
      = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x
          (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y z)
  rw [hY]
  exact Work.Cohomology.cupAssoc 𝕜 (Work.SSS.sSing E) x y z

/-- **Associativity of the product on the pages, for any product that is associative on the
underlying filtered complex.** -/
theorem pd_mul_assoc_gen {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜}
    (hassoc : ∀ (n m k : ℕ) (x : W.C.X n) (y : W.C.X m) (z : W.C.X k),
      W.xcast (Nat.add_assoc n m k) (W.mul (n+m) k (W.mul n m x y) z)
        = W.mul n (m+k) x (W.mul m k y z))
    (r s n s' n' s'' n'' : ℕ)
    (x : pEraw 𝕜 W r s n) (y : pEraw 𝕜 W r s' n') (z : pEraw 𝕜 W r s'' n'') :
    (pEcast 𝕜 W r (show (s + s') + s'' = s + (s' + s'') from by omega)
        (show (n + n') + n'' = n + (n' + n'') from by omega)).hom
      (pd_mul r (s + s') (n + n') s'' n'' (pd_mul r s n s' n' x y) z)
    = pd_mul r s n (s' + s'') (n' + n'') x (pd_mul r s' n' s'' n'' y z) := by
  obtain ⟨x₀, rfl⟩ :=
    Submodule.mkQ_surjective ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x
  obtain ⟨y₀, rfl⟩ :=
    Submodule.mkQ_surjective ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) y
  obtain ⟨z₀, rfl⟩ :=
    Submodule.mkQ_surjective ((pDen 𝕜 W r s'' n'').comap (pZ 𝕜 W r s'' n'').subtype) z
  rw [pd_mul_nat r s n s' n' x₀ y₀,
    pd_mul_nat r (s + s') (n + n') s'' n''
      (pd_mulZ r s n s' n' x₀ y₀) z₀,
    pd_pEcast_mkQ' (show (s + s') + s'' = s + (s' + s'') from by omega)
      (show (n + n') + n'' = n + (n' + n'') from by omega)
      (pd_mulZ r (s + s') (n + n') s'' n'' (pd_mulZ r s n s' n' x₀ y₀) z₀),
    pd_mul_nat r s' n' s'' n'' y₀ z₀,
    pd_mul_nat r s n (s' + s'') (n' + n'') x₀ (pd_mulZ r s' n' s'' n'' y₀ z₀)]
  apply pd_mkQ_congr
  simp only [pd_mulZ_val]
  exact hassoc n n' n'' (x₀ : W.C.X n) (y₀ : W.C.X n') (z₀ : W.C.X n'')

theorem pdMulAssoc (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (r s n s' n' s'' n'' : ℕ)
    (x : Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r s n)
    (y : Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r s' n')
    (z : Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r s'' n'') :
    (Work.Pi6.MSS.pEcast 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r
        (show (s + s') + s'' = s + (s' + s'') from by omega)
        (show (n + n') + n'' = n + (n' + n'') from by omega)).hom
      (Work.Pi6.MSS.pd_mul r (s + s') (n + n') s'' n''
        (Work.Pi6.MSS.pd_mul r s n s' n' x y) z)
    = Work.Pi6.MSS.pd_mul r s n (s' + s'') (n' + n'') x
        (Work.Pi6.MSS.pd_mul r s' n' s'' n'' y z) :=
  pd_mul_assoc_gen (serreCF_xcast_mul 𝕜 E B p) r s n s' n' s'' n'' x y z

end

end Work.Pi6.MSS

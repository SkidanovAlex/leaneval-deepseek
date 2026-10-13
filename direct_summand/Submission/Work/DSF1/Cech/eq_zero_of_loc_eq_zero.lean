import Mathlib
import Submission.Work.DSF1.Cech.CechDefs
import Submission.Work.DSF1.Cech.basicOpen_localization_facts
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSF1.Cech.isIsoDeletion_Qi
import Submission.Work.DSF1.Cech.CoaugCycle

/-!
# Injectivity of `locᵢ` up to powers of `f i`

Let `R` be a commutative ring, `f : ι → R` a finite family and `U i = D (f i)`
the associated principal opens of `X = Spec R`.  The chain map
`locᵢ : 𝒞 ⟶ 𝒞ᵢ` (`CechDefs.loc`) is induced by the restriction
`P W ⟶ P (W ⊓ U i)` of the structure sheaf (viewed as a presheaf of `R`-modules).

Since `Γ (W ⊓ D (f i))` is the localization of `Γ W` away from `f i` when `W` is a
basic open (`basicOpen_localization_facts`), the kernel of `locᵢ` consists of
elements killed by a power of `f i`:

`(loc f i).f n t = 0 → ∃ k, f i ^ k • t = 0`.

The proof is componentwise.  In degree `n` both `𝒞` and `𝒞ᵢ` are products over the
simplices `x : Fin (n+1) → ι`, with `x`-component `Γ (Eobj U n x)`.  Each open
`Eobj U n x = ⨅ a, U (x a) = D (∏ a, f (x a))` is a basic open, so the local
statement applies to every component; because there are finitely many components one
can clear all denominators at once.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

namespace Work.DSF1.Cech

universe u v

/-! ## Elementary facts about opens and about products of modules -/

/-- In the lattice of opens of a topological space, the categorical product of a family
of opens is its infimum. -/
lemma piObj_eq_iInf {X : Type*} [TopologicalSpace X] {β : Type*}
    (U : β → TopologicalSpace.Opens X) [HasProduct U] : ∏ᶜ U = ⨅ b, U b := by
  apply le_antisymm
  · exact le_iInf (fun b => leOfHom (Pi.π U b))
  · exact leOfHom (Pi.lift (fun b => homOfLE (iInf_le U b)))

/-- `PrimeSpectrum.basicOpen` turns finite products into finite infima. -/
lemma basicOpen_finset_prod {R : Type u} [CommRing R] {β : Type v} (s : Finset β)
    (h : β → R) :
    PrimeSpectrum.basicOpen (s.prod h) = s.inf (fun b => PrimeSpectrum.basicOpen (h b)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PrimeSpectrum.basicOpen_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, PrimeSpectrum.basicOpen_mul, Finset.inf_insert, ih]

/-- `PrimeSpectrum.basicOpen` of a product indexed by `Fin k` is the infimum of the
basic opens. -/
lemma basicOpen_fin_prod {R : Type u} [CommRing R] {k : ℕ} (h : Fin k → R) :
    PrimeSpectrum.basicOpen (∏ a : Fin k, h a) = ⨅ a : Fin k, PrimeSpectrum.basicOpen (h a) := by
  have h1 := basicOpen_finset_prod (R := R) (s := (Finset.univ : Finset (Fin k))) h
  rw [Finset.inf_univ_eq_iInf] at h1
  exact h1

/-- Two elements of a product of modules coincide as soon as all their components do. -/
lemma pi_ext {R : Type u} [CommRing R] {β : Type u} {F : β → ModuleCat.{u} R} [HasProduct F]
    {a b : ↥(∏ᶜ F)}
    (h : ∀ x, (Pi.π F x : (∏ᶜ F : ModuleCat.{u} R) ⟶ F x).hom a =
              (Pi.π F x : (∏ᶜ F : ModuleCat.{u} R) ⟶ F x).hom b) : a = b := by
  have key : ∀ w : ↥(∏ᶜ F),
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R ↥(∏ᶜ F) w)).hom (1 : R) = w := by
    intro w
    simp [LinearMap.toSpanSingleton_apply]
  have h2 : ModuleCat.ofHom (LinearMap.toSpanSingleton R ↥(∏ᶜ F) a) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R ↥(∏ᶜ F) b) := by
    apply Pi.hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, key, key]
    exact h x
  have := congrArg (fun (f : ModuleCat.of R R ⟶ ∏ᶜ F) => f.hom 1) h2
  rwa [key, key] at this

/-! ## The local statement on a basic open -/

/-- **The kernel of the restriction is `f`-power torsion.**  A section of the structure
sheaf of `Spec R` over `D G` which restricts to `0` on `D G ⊓ D g = D (G g)` is killed
by a power of `g`.  This is the second half of `basicOpen_localization_facts` rewritten
in terms of the module structure of `specPresheaf`. -/
theorem resSection_eq_zero_imp_pow_smul_eq_zero {R : Type u} [CommRing R] (G g : R)
    (s : (specPresheaf R).obj (op (PrimeSpectrum.basicOpen G)))
    (h : ((specPresheaf R).map (homOfLE (inf_le_left :
        PrimeSpectrum.basicOpen G ⊓ PrimeSpectrum.basicOpen g ≤
          PrimeSpectrum.basicOpen G)).op).hom s = 0) :
    ∃ k : ℕ, g ^ k • s = 0 := by
  have h' : resSection R (inf_le_left : PrimeSpectrum.basicOpen G ⊓ PrimeSpectrum.basicOpen g ≤
      PrimeSpectrum.basicOpen G) s = 0 := by
    rw [← specPresheaf_map_apply]
    exact h
  obtain ⟨k, hk⟩ := (basicOpen_localization_facts R G g).2 s h'
  refine ⟨k, ?_⟩
  rw [smul_eq_algebraMap_mul, map_pow, mul_comm,
    ← resSection_le_top_GammaSpecIso_inv R (PrimeSpectrum.basicOpen G) g]
  exact hk

/-- The same statement for an open which is only *equal* to a basic open. -/
lemma loc_comp_kernel {R : Type u} [CommRing R] (G g : R) (W : (spec R).Opens)
    (hW : W = PrimeSpectrum.basicOpen G) (s : (specPresheaf R).obj (op W))
    (hs : ((specPresheaf R).map (homOfLE (inf_le_left :
        W ⊓ PrimeSpectrum.basicOpen g ≤ W)).op).hom s = 0) :
    ∃ k : ℕ, g ^ k • s = 0 := by
  subst hW
  exact resSection_eq_zero_imp_pow_smul_eq_zero G g s hs

/-- The simplex `x` of the Čech nerve gives the basic open `D (∏ a, f (x a))`. -/
lemma Eobj_basicOpens_eq {R : Type u} [CommRing R] {ι : Type u} (f : ι → R) (n : ℕ)
    (x : ((FormalCoproduct.mk ι (basicOpens f)).cech.obj (op ⦋n⦌)).I) :
    Eobj (basicOpens f) n x = PrimeSpectrum.basicOpen (∏ a : Fin (n+1), f (x a)) := by
  rw [show Eobj (basicOpens f) n x = ∏ᶜ (basicOpens f ∘ x) from rfl, piObj_eq_iInf]
  rw [show (⨅ a : Fin (n+1), (basicOpens f ∘ x) a) =
        ⨅ a : Fin (n+1), PrimeSpectrum.basicOpen (f (x a)) from rfl,
    ← basicOpen_fin_prod]

/-! ## The main statement -/

theorem eq_zero_of_loc_eq_zero {R : Type u} [CommRing R] {ι : Type u} [Fintype ι]
    (f : ι → R) (i : ι) (n : ℕ) (t : (Work.DSF1.Cech.cechSpec f).X n)
    (h : (Work.DSF1.Cech.loc f i).f n t = 0) : ∃ k : ℕ, f i ^ k • t = 0 := by
  let F : ((FormalCoproduct.mk ι (basicOpens f)).cech.obj (op ⦋n⦌)).I → ModuleCat.{u} R :=
    fun y => (specPresheaf R).obj (op (Eobj (basicOpens f) n y))
  -- For each simplex `x`, some power of `f i` kills the `x`-component of `t`.
  have hstep : ∀ x, ∃ k : ℕ, f i ^ k • ((Pi.π F x).hom t) = 0 := by
    intro x
    -- The `x`-component of `(loc f i).f n t` is the restriction of that component to `U i`.
    have hA : ((etaI (basicOpens f) (specPresheaf R) i).app
          (op (Eobj (basicOpens f) n x))).hom ((Pi.π F x).hom t) = 0 := by
      have hmap := cechComplexFunctor_map_pi (basicOpens f)
        (etaI (basicOpens f) (specPresheaf R) i) n x
      have key := congrArg (fun m => ModuleCat.Hom.hom m t) hmap
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at key
      have hl : (((cechComplexFunctor (basicOpens f)).map
          (etaI (basicOpens f) (specPresheaf R) i)).f n).hom t = 0 := h
      rw [hl, map_zero] at key
      exact key.symm
    rw [show (etaI (basicOpens f) (specPresheaf R) i).app (op (Eobj (basicOpens f) n x))
        = (specPresheaf R).map (homOfLE (inf_le_left :
            Eobj (basicOpens f) n x ⊓ basicOpens f i ≤ Eobj (basicOpens f) n x)).op
          from rfl] at hA
    exact loc_comp_kernel (∏ a : Fin (n+1), f (x a)) (f i) (Eobj (basicOpens f) n x)
      (Eobj_basicOpens_eq f n x) _ hA
  choose K hK using hstep
  letI : Fintype ((FormalCoproduct.mk ι (basicOpens f)).cech.obj (op ⦋n⦌)).I :=
    inferInstanceAs (Fintype (Fin (n+1) → ι))
  -- Clear all denominators at once.
  refine ⟨Finset.univ.sup K, ?_⟩
  apply pi_ext (F := F)
  intro x
  rw [map_smul, map_zero]
  have hle : K x ≤ Finset.univ.sup K := Finset.le_sup (Finset.mem_univ x)
  have hp : f i ^ (Finset.univ.sup K) = f i ^ (Finset.univ.sup K - K x) * f i ^ (K x) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hp, mul_smul, hK x, smul_zero]

end Work.DSF1.Cech

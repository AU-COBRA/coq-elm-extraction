{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "ElmExtraction";

  default-bundle = "9.0";

  bundles."9.0" = {
    coqPackages.coq.override.version = "9.0";
    coqPackages.metarocq.override.version = "1.4-9.0";
  };
  bundles."9.1" = {
    coqPackages.coq.override.version = "9.1";
    coqPackages.metarocq.override.version = "1.4-9.1";
  };

  bundles."9.0".push-branches = ["master"];
  bundles."9.1".push-branches = ["master"];

  ## Cachix caches to use in CI
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metarocq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}
